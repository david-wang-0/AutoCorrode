#!/usr/bin/env python3
"""Show a proof method diverging at the end of a chain of theories after an upstream change,
and how I/Q's stall detection and cancel_command deal with it.

Self-contained: by default the script generates a fresh auth token, launches its own
Isabelle/jEdit on this directory with that token, finds the port the I/Q plugin picked,
runs the demo, and shuts jEdit down again. Nothing of yours is touched; the only
requirements are `isabelle` on PATH (or --isabelle / $ISABELLE_HOME) with the I/Q plugin
installed, and the HOL heap (built on first use if missing).

Fixture (this directory): A -> B -> C -> D. A.thy carries a commented-out pair of simp rules
`foo n = bar n`, `bar n = foo n`. Uncommenting them is a harmless-looking upstream change:
A, B and C stay green, but the first `simp` on a `foo` term is in D, where the simplifier now
rewrites foo -> bar -> foo forever. A proof method has no timeout of its own, so without
intervention the prover spins until jEdit is killed.

Steps:

  1. authenticate, check the server has `cancel_command` (the stall-cancel build)
  2. open A..D and drive the chain to green as a baseline (bounded wait on D)
  3. write_file: enable the rules in A -- the "upstream change"
  4. THE STALL: a bounded `get_diagnostics wait_until_processed:true` on D returns EARLY
     with `stalled: true` and names the running command in `running_commands`, instead
     of sitting for its whole `timeout`; two `get_processing_status` reads show `finished`
     frozen with `running: 1` and `elapsed_ms` growing
  5. THE FIX: `cancel_command scope:running` on D interrupts the tactic at once
  6. cancellation is not sticky (PIDE re-runs the command at the next document update),
     so the rules are commented out again and the chain is driven back to green

Limitation worth knowing: only the waited theory is watched. Interactive PIDE forks
terminal proofs, so had the looping `simp` been in C, D would still have been processed
and a wait on D would have completed without noticing C spinning. Wait on (or read
`get_processing_status` of) the theory where the proof lives.

Usage:
  demo_stall.py                       launch a private jEdit, run, shut it down
  demo_stall.py --keep-jedit          same, but leave jEdit running (port + token printed)
  demo_stall.py --attach PORT         use an already running jEdit; IQ_AUTH_TOKEN must be set
Options: --timeout MS (one bounded wait, default 30000), --stall MS (stall threshold, default 5000),
         --max-wait S (keep waiting while progressing, default 1800), --keep-stalled,
         --isabelle PATH, --startup-timeout S (default 600)
"""

import argparse
import json
import os
import secrets
import signal
import socket
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHAIN = ["A", "B", "C", "D"]
THY = {name: str(HERE / f"{name}.thy") for name in CHAIN}
RULE = 'lemma foo_loop [simp]: "foo n = bar n" "bar n = foo n" by (simp_all add: foo_def bar_def)'
RULE_OFF = f"(* {RULE} *)"
BASE_PORT = 8765          # the plugin scans upward from here for a free port
PORT_SCAN = 16


# --- I/Q client -----------------------------------------------------------------------------

class IQ:
    """Minimal newline-delimited JSON-RPC client for the I/Q TCP server."""

    def __init__(self, port: int, io_timeout: float):
        self.sock = socket.create_connection(("127.0.0.1", port), timeout=io_timeout)
        self.buf = b""
        self.next_id = 0

    def close(self) -> None:
        try:
            self.sock.close()
        except OSError:
            pass

    def rpc(self, method: str, params: dict) -> dict:
        self.next_id += 1
        req = {"jsonrpc": "2.0", "id": self.next_id, "method": method, "params": params}
        self.sock.sendall((json.dumps(req) + "\n").encode())
        while True:
            while b"\n" not in self.buf:
                chunk = self.sock.recv(1 << 16)
                if not chunk:
                    raise RuntimeError("I/Q closed the connection")
                self.buf += chunk
            line, self.buf = self.buf.split(b"\n", 1)
            msg = json.loads(line)
            if msg.get("id") == self.next_id:
                break  # skip notifications
        if "error" in msg:
            raise RuntimeError(f"{method}: {msg['error']}")
        return msg["result"]

    def call(self, tool: str, **args) -> dict:
        """tools/call; the server returns the result map as JSON text in content[0].text."""
        res = self.rpc("tools/call", {"name": tool, "arguments": args})
        text = res["content"][0]["text"]
        try:
            payload = json.loads(text)
        except json.JSONDecodeError:
            payload = {"text": text}
        if res.get("isError"):
            raise RuntimeError(f"{tool} failed: {payload}")
        return payload

    def tool_names(self) -> set:
        return {t["name"] for t in self.rpc("tools/list", {})["tools"]}


# --- launching jEdit ------------------------------------------------------------------------

def isabelle_exe(explicit: str | None) -> str:
    if explicit:
        return explicit
    home = os.environ.get("ISABELLE_HOME")
    if home and (Path(home) / "bin" / "isabelle").exists():
        return str(Path(home) / "bin" / "isabelle")
    return "isabelle"


def launch_jedit(isabelle: str, token: str) -> tuple[subprocess.Popen, str]:
    """Start a private jEdit on this directory. IQ_AUTH_TOKEN is how the plugin learns the
    token; IQ_MCP_ALLOWED_ROOTS lets write_file/cancel_command touch the fixture.
    -noserver keeps it from joining/replacing a jEdit you may already have open."""
    env = dict(os.environ, IQ_AUTH_TOKEN=token, IQ_MCP_ALLOWED_ROOTS=str(HERE))
    log_fd, log_path = tempfile.mkstemp(prefix="iq-stall-demo-", suffix=".log")
    cmd = [isabelle, "jedit", "-d", ".", "-l", "HOL", "-j", "-noserver", "D.thy"]
    proc = subprocess.Popen(cmd, cwd=HERE, env=env, stdout=log_fd, stderr=subprocess.STDOUT,
                            stdin=subprocess.DEVNULL, start_new_session=True)
    os.close(log_fd)
    print(f"  launched: {' '.join(cmd)}  (pid {proc.pid}, log {log_path})")
    return proc, log_path


def find_our_port(token: str, proc: subprocess.Popen, startup_s: float) -> int:
    """Scan BASE_PORT.. for the I/Q instance that accepts OUR token. Other I/Q servers on
    this machine (another project's jEdit) reject it, so the token doubles as identity."""
    deadline = time.monotonic() + startup_s
    while time.monotonic() < deadline:
        if proc.poll() is not None:
            raise RuntimeError(f"jEdit exited with status {proc.returncode} before I/Q came up")
        for port in range(BASE_PORT, BASE_PORT + PORT_SCAN):
            try:
                iq = IQ(port, io_timeout=5)
            except OSError:
                continue
            try:
                names = iq.tool_names()
                if "authenticate" in names:
                    iq.call("authenticate", token=token)
                    return port
            except Exception:  # noqa: BLE001 - wrong instance, not ready, or wrong token
                pass
            finally:
                iq.close()
        time.sleep(2)
    raise RuntimeError(f"no I/Q server accepted the token within {startup_s:.0f} s")


def processes_with_token(token: str) -> list[int]:
    """Every process whose environment carries our IQ_AUTH_TOKEN: the isabelle wrapper, the
    JVM it execs, the Poly/ML prover and helpers, however they re-parented. Linux only."""
    needle = f"IQ_AUTH_TOKEN={token}".encode()
    pids = []
    for entry in Path("/proc").iterdir():
        if not entry.name.isdigit() or int(entry.name) == os.getpid():
            continue
        try:
            if needle in (entry / "environ").read_bytes():
                pids.append(int(entry.name))
        except OSError:
            continue
    return pids


def stop_jedit(proc: subprocess.Popen, token: str) -> None:
    """The isabelle wrapper spawns the JVM, which can outlive the wrapper's process group,
    so signal the group first and then everything still tagged with our token."""
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    try:
        proc.wait(timeout=15)
    except subprocess.TimeoutExpired:
        pass
    for sig, grace in ((signal.SIGTERM, 15), (signal.SIGKILL, 5)):
        pids = processes_with_token(token)
        if not pids:
            break
        for pid in pids:
            try:
                os.kill(pid, sig)
            except ProcessLookupError:
                pass
        deadline = time.monotonic() + grace
        while time.monotonic() < deadline and processes_with_token(token):
            time.sleep(0.5)
    left = processes_with_token(token)
    print("  jEdit stopped" if not left else f"  WARNING: processes still alive: {left}")


# --- helpers --------------------------------------------------------------------------------

def banner(text: str) -> None:
    print(f"\n=== {text}")


def fmt_running(entries) -> str:
    return "; ".join(
        f"line {c.get('line')} after {c.get('elapsed_ms')} ms: {str(c.get('source_preview', '')).strip()[:48]}"
        for c in entries or []
    )


def wait_tracked(iq: IQ, name: str, settle_s: float) -> None:
    """Right after start-up the session has not parsed the theories yet."""
    deadline = time.monotonic() + settle_s
    while time.monotonic() < deadline:
        try:
            if "finished" in iq.call("get_processing_status", path=THY[name]):
                return
        except RuntimeError:  # "No file found matching ..." until the session has loaded it
            pass
        time.sleep(2)
    raise RuntimeError(f"{name}.thy is not tracked by the session after {settle_s:.0f} s")


def open_as_buffer(iq: IQ, name: str, settle_s: float = 30.0) -> None:
    """open_file returns before jEdit has finished loading the buffer and PIDE has attached
    a buffer model to it; write_file needs that model. Poll list_files until it is there."""
    iq.call("open_file", path=THY[name], view=True)
    deadline = time.monotonic() + settle_s
    while time.monotonic() < deadline:
        for f in iq.call("list_files").get("files", []):
            if f.get("path") == THY[name] and f.get("model_type") == "buffer":
                return
        time.sleep(0.5)
    raise RuntimeError(f"{name}.thy did not become a jEdit buffer within {settle_s:.0f} s")


def status(iq: IQ, name: str) -> dict:
    st = iq.call("get_processing_status", path=THY[name])
    line = (f"  {name}: finished={st.get('finished')} running={st.get('running')} "
            f"unprocessed={st.get('unprocessed')} errors={st.get('error_count')}")
    if st.get("running_commands"):
        line += f"  <- running: {fmt_running(st['running_commands'])}"
    print(line)
    return st


def wait_on(iq: IQ, name: str, timeout_ms: int, stall_ms: int) -> dict:
    t0 = time.monotonic()
    d = iq.call("get_diagnostics", path=THY[name], severity="error", scope="file",
                wait_until_processed=True, timeout=timeout_ms, timeout_per_command=stall_ms)
    dt = time.monotonic() - t0
    fs = d.get("file_summary", {})
    w = d.get("wait", {})  # the wait outcome: completed / timed_out / stalled / running_commands
    print(f"  wait on {name} returned after {dt:.1f} s: completed={w.get('completed')} "
          f"timed_out={w.get('timed_out')} stalled={w.get('stalled')} "
          f"errors={fs.get('errors')} fully_processed={fs.get('fully_processed')}")
    if w.get("running_commands"):
        print(f"    running_commands: {fmt_running(w['running_commands'])}")
    return w


def wait_until_done(iq: IQ, name: str, timeout_ms: int, stall_ms: int, max_s: float) -> dict:
    """Drive a theory to completion however long it takes: keep issuing bounded waits while
    PIDE is making progress, and stop only on completed or stalled. A single bounded wait
    would report timed_out on any theory that honestly needs longer than its timeout; with
    the stall detector, timed_out-without-stalled means progress, so waiting on is safe."""
    deadline = time.monotonic() + max_s
    rounds = 0
    while True:
        w = wait_on(iq, name, timeout_ms, stall_ms)
        rounds += 1
        if w.get("completed") or w.get("stalled"):
            if rounds > 1:
                print(f"  ({rounds} bounded waits)")
            return w
        if time.monotonic() >= deadline:
            print(f"  gave up after {max_s:.0f} s: still progressing but not complete")
            return w
        status(iq, name)  # timed out without stalling = progress; show it and wait again


def set_rule(iq: IQ, enabled: bool) -> None:
    old, new = (RULE_OFF, RULE) if enabled else (RULE, RULE_OFF)
    r = iq.call("write_file", path=THY["A"], command="str_replace", old_str=old, new_str=new,
                wait_until_processed=False)
    if r.get("edits_failed"):
        raise RuntimeError(f"write_file could not flip the rule: {r}")
    print(f"  A.thy: foo_loop [simp] is now {'ENABLED' if enabled else 'commented out'}")


# --- the demo -------------------------------------------------------------------------------

def run_demo(iq: IQ, args) -> int:
    banner("2. open the chain and get it green as a baseline")
    wait_tracked(iq, "D", settle_s=120)
    for name in CHAIN:
        open_as_buffer(iq, name)
    base = wait_until_done(iq, "D", args.timeout, args.stall, args.max_wait)
    if not base.get("completed"):
        sys.exit("baseline did not complete (stalled or over --max-wait); are the rules already "
                 "uncommented in A.thy?")
    for name in CHAIN:
        status(iq, name)

    rule_on = False
    try:
        banner("3. the upstream change: enable the looping simp rules in A")
        set_rule(iq, True)
        rule_on = True

        banner(f"4. THE STALL: bounded wait on D (timeout {args.timeout} ms, stall threshold {args.stall} ms)")
        w = wait_until_done(iq, "D", args.timeout, args.stall, args.max_wait)
        if w.get("stalled"):
            print("  -> returned early with stalled=true and named the diverging command; without the "
                  "detector this call would have sat for its whole timeout and reported only timed_out")
        else:
            print(f"  -> NOTE: stalled not reported (timed_out={w.get('timed_out')}); showing the counts anyway")
        s1 = status(iq, "D")
        time.sleep(3)
        s2 = status(iq, "D")
        if s1.get("finished") == s2.get("finished") and (s2.get("running") or 0) >= 1:
            print("  -> finished is frozen, running >= 1, elapsed_ms keeps growing: a diverging method. "
                  "simp has no timeout; this spins until interrupted")

        if args.keep_stalled:
            print("\n--keep-stalled: leaving the method running and the rules enabled")
            rule_on = False  # deliberately not restored
            return 0

        banner("5. THE FIX: cancel_command scope:running on D")
        r = iq.call("cancel_command", path=THY["D"], scope="running")
        for e in r.get("canceled") or []:
            print(f"  canceled: line {e.get('line')} offset {e.get('offset')}, "
                  f"{e.get('execs_canceled')} exec(s): {str(e.get('source_preview', '')).strip()[:48]}")
        if r.get("still_running"):
            print(f"  still running: {fmt_running(r['still_running'])}")
        print(f"  note: {r.get('note')}")
        time.sleep(1)
        status(iq, "D")

        banner("6. make it stick: comment the rules out again and drive the chain back to green")
        set_rule(iq, False)
        rule_on = False
        final = wait_until_done(iq, "D", args.timeout, args.stall, args.max_wait)
        for name in CHAIN:
            status(iq, name)
        ok = bool(final.get("completed")) and not final.get("stalled")
        print("\nRESULT:", "chain is green again" if ok else "chain did not come back green")
        return 0 if ok else 1
    finally:
        if rule_on:
            print("\ncleanup: restoring A.thy")
            try:
                iq.call("cancel_command", path=THY["D"], scope="running")
                set_rule(iq, False)
            except Exception as e:  # noqa: BLE001
                print(f"  cleanup failed: {e}; fix A.thy by hand")


def main() -> int:
    ap = argparse.ArgumentParser(description="I/Q stall detection demo on the A->B->C->D fixture")
    ap.add_argument("--attach", type=int, metavar="PORT",
                    help="use an already running jEdit on this port (IQ_AUTH_TOKEN must be set) instead of launching one")
    ap.add_argument("--isabelle", help="isabelle executable (default: $ISABELLE_HOME/bin/isabelle or PATH)")
    ap.add_argument("--startup-timeout", type=int, default=600,
                    help="seconds to wait for the launched jEdit's I/Q server (default 600; building HOL takes longer)")
    ap.add_argument("--keep-jedit", action="store_true", help="leave the launched jEdit running")
    ap.add_argument("--timeout", type=int, default=30000, help="overall wait per call, ms (default 30000)")
    ap.add_argument("--stall", type=int, default=5000,
                    help="timeout_per_command stall threshold, ms (default 5000)")
    ap.add_argument("--max-wait", type=int, default=1800,
                    help="seconds to keep re-issuing bounded waits while a theory is still progressing (default 1800)")
    ap.add_argument("--keep-stalled", action="store_true",
                    help="stop after the stall is shown; leave the rules enabled and the method running")
    args = ap.parse_args()

    proc = None
    if args.attach:
        token = os.environ.get("IQ_AUTH_TOKEN", "").strip()
        if not token:
            sys.exit("--attach needs IQ_AUTH_TOKEN in the environment")
        port = args.attach
        banner(f"1. attach to the I/Q server on port {port}")
    else:
        token = secrets.token_urlsafe(24)
        banner("1. launch a private Isabelle/jEdit with a fresh auth token")
        proc, _ = launch_jedit(isabelle_exe(args.isabelle), token)
        port = find_our_port(token, proc, args.startup_timeout)
        print(f"  I/Q is up on port {port}")

    iq = IQ(port, io_timeout=args.timeout / 1000 + 60)
    try:
        iq.call("authenticate", token=token)
        if "cancel_command" not in iq.tool_names():
            sys.exit("this I/Q build has no cancel_command / stall detection; install the current plugin first")
        print("  authenticated; server has cancel_command")
        return run_demo(iq, args)
    finally:
        iq.close()
        if proc is not None:
            if args.keep_jedit or args.keep_stalled:
                print(f"\njEdit left running: pid {proc.pid}, port {port}, IQ_AUTH_TOKEN={token}")
            else:
                banner("shutting the private jEdit down")
                stop_jedit(proc, token)


if __name__ == "__main__":
    sys.exit(main())
