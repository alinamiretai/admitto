#!/usr/bin/env python3
"""
Differential validation: does Admitto's typed capability model agree with real
OS filesystem permissions, on the domain where the two abstractions are
comparable?

Admitto models a LINEAR authority hierarchy (read < write < exec): holding a
level implies holding all lower levels. Unix uses INDEPENDENT permission bits.
The two are comparable exactly on CUMULATIVE permission sets:
  read-only (r--), read+write (rw-), read+write+exec (rwx).
We validate the model against real OS behavior on those, and separately report
the independent-bit cases as outside the model's abstraction.
"""
import os, stat, subprocess, tempfile

def model_admits(held, requested):
    r = subprocess.run(
        ["lake", "exe", "admitto-agent", "/x", held, requested],
        capture_output=True, text=True
    )
    return r.returncode == 0  # 0 = ADMIT, 1 = DENY

def os_allows(bits, op):
    fd, path = tempfile.mkstemp(); os.close(fd)
    try:
        os.chmod(path, bits)
        try:
            if op == "read":
                with open(path, "r") as f: f.read(1); return True
            elif op == "write":
                with open(path, "a") as f: f.write("x"); return True
            elif op == "exec":
                return os.access(path, os.X_OK)
        except (PermissionError, OSError):
            return False
    finally:
        os.chmod(path, 0o600); os.remove(path)

# The comparable domain: cumulative permission sets matching the linear model.
CUMULATIVE = {
    "read":  stat.S_IRUSR,
    "write": stat.S_IRUSR | stat.S_IWUSR,
    "exec":  stat.S_IRUSR | stat.S_IWUSR | stat.S_IXUSR,
}
OPS = ["read", "write", "exec"]

def main():
    agree, disagree = 0, []
    print("=== Admitto typed-capability model vs. real OS (cumulative domain) ===\n")
    print(f"{'held':>6} {'op':>6} {'OS':>7} {'model':>7} {'':>4}")
    for held, bits in CUMULATIVE.items():
        for op in OPS:
            osr = os_allows(bits, op)
            mr = model_admits(held, op)
            ok = (osr == mr)
            if ok: agree += 1
            else: disagree.append((held, op, osr, mr))
            print(f"{held:>6} {op:>6} {str(osr):>7} {str(mr):>7} {'ok' if ok else 'DIFF':>4}")
    total = agree + len(disagree)
    print(f"\nAgreements on comparable domain: {agree}/{total}")
    if not disagree:
        print("Model faithfully matches real OS on the cumulative permission hierarchy.")
    else:
        print("Divergences (worth investigating):", disagree)
    print("\nNote: Unix independent-bit permissions (e.g. exec-without-read) are")
    print("outside the linear model's abstraction and are not claimed to be covered.")

if __name__ == "__main__":
    main()
