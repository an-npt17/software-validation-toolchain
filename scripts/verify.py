import os
import subprocess
import tempfile
import json
import re


def eval_vercors(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".pvl", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/home",
        "-w",
        "/home",
        "vercors:try",
        "vct",
        container_file_path,
    ]

    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr
        if not timed_out
        else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": (not timed_out) and completed.returncode == 2,
        "partial": not timed_out
        and (not (completed.returncode == 2) or not (completed.returncode == 0)),
    }


def eval_cbmc(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".c", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/home",
        "-w",
        "/home",
        "cbmc:try",
        "cbmc",
        "-z3",
        container_file_path,
    ]

    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    match = re.search(r"\b(\d+)\s+of\s+(\d+)\s+failed\b", str(completed.stdout))
    partial = True
    none_verified = False
    if match:
        failed, total = int(match.group(1)), int(match.group(2))
        none_verified = failed == total
        partial = failed < total

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr
        if not timed_out
        else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out)
        and (completed.returncode == 0)
        and not none_verified,
        "timed_out": timed_out,
        "compilation_err": (not timed_out) and (completed.returncode == 6),
        "partial": (not timed_out) and (not completed.returncode == 6) and partial,
    }


def eval_verifast(
    code, timeout=5, language="java", max_errs=5, json_mode=True, func_name=None
) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=f".{language}", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/home",
        "-w",
        "/home",
        "verifast:try",
        "verifast",
        "-c",
        "-disable_overflow_check",
        container_file_path,
    ]

    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    match = re.search(
        r"(\d+)\s+errors\s+found\s+\((\d+)\s+statements\s+verified\)",
        str(completed.stdout),
    )

    partial = True
    goals = False
    if match:
        errors = int(match.group(1))
        verified = int(match.group(2))
        partial = errors != 0
        goals = verified > 0

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr
        if not timed_out
        else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out)
        and (completed.returncode == 0)
        and not partial
        and goals,
        "timed_out": timed_out,
        "compilation_err": (not timed_out) and (completed.returncode == 1),
        "partial": not timed_out and partial and goals,
    }


def eval_why3(
    code, timeout=60, timelimit=10, max_errs=5, json_mode=True, func_name=None
) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".mlw", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/home",
        "-w",
        "/home",
        "why3:try",
        "why3",
        "prove",
        "-P",
        "cvc4",
        "--timelimit",
        f"{timelimit}",
        container_file_path,
    ]
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr
        if not timed_out
        else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode == 1),
        "partial": (not timed_out and completed.returncode == 2),
    }


def eval_dafny(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".dfy", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/home",
        "-w",
        "/home",
        "dafny:try",
        "dafny",
        "verify",
        "--allow-warnings",
        container_file_path,
    ]
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr
        if not timed_out
        else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode == 2),
        "partial": not timed_out and (completed.returncode == 4),
    }


def eval_verus(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".dfy", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    multiple_errors = f"--multiple-errors {max_errs}" if max_errs > 0 else ""
    err_format = "--output-json --error-format=json" if json_mode else ""
    cmd = (f"/verus/verus {multiple_errors} {err_format}").split(" ")
    cmd += [filename]
    if func_name:
        cmd += ["--verify-function", func_name, "--verify-root"]

    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/home",
        "-w",
        "/home",
        "verus:try",
    ] + cmd

    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr
        if not timed_out
        else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out) and (completed.returncode == 0),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode == 1),
        "partial": not timed_out
        and (completed.returncode != 0)
        and (completed.returncode != 1),
    }


def eval_framac(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".c", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)

    container_file_path = f"/home/{filename}"

    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/home",
        "-w",
        "/home",
        "framac:try",
        "frama-c",
        "-wp",
        "-wp-rte",
        "-wp-prover",
        "alt-ergo",
        container_file_path,
    ]
    try:
        completed = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,  # seconds
        )
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    os.unlink(f.name)

    partial = True
    no_goal = True
    match = re.search(r"Proved goals:\s+(\d+)\s*/\s*(\d+)", str(completed.stdout))
    if match:
        proved, total = int(match.group(1)), int(match.group(2))
        no_goal = total == 0
        partial = proved < total

    return {
        "out": completed.stdout if not timed_out else "",
        "err": completed.stderr
        if not timed_out
        else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": (not timed_out)
        and (completed.returncode == 0)
        and (not partial)
        and (not no_goal),
        "timed_out": timed_out,
        "compilation_err": not timed_out and (completed.returncode != 0),
        "partial": not timed_out and (partial or no_goal),
    }


def eval_spin(code, timeout=60, max_errs=5, json_mode=True, func_name=None) -> dict:
    """
    Evaluate Promela code using SPIN model checker.

    SPIN verification process:
    1. spin -a model.pml  - Generate verifier (creates pan.c)
    2. gcc -o pan pan.c   - Compile verifier
    3. ./pan -a          - Run verification

    The function checks for:
    - Syntax errors (spin -a fails)
    - Compilation errors (gcc fails)
    - Verification results (pan output)
    - LTL property violations
    - Deadlocks
    - Assertion violations
    """
    tmp_dir = os.getcwd()
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".pml", dir=tmp_dir, delete=False
    ) as f:
        f.write(code)
        filename = os.path.basename(f.name)
        base_name = filename.replace(".pml", "")

    container_file_path = f"/workspace/{filename}"

    # Multi-stage SPIN verification in Docker
    # Stage 1: Generate verifier with spin -a
    # Stage 2: Compile verifier with gcc
    # Stage 3: Run verification with ./pan

    cmd = [
        "docker",
        "run",
        "--rm",
        "-v",
        f"{tmp_dir}:/workspace",
        "-w",
        "/workspace",
        "spin:try",
        "bash",
        "-c",
        f"spin -a {filename} && gcc -o pan pan.c && ./pan -a -f -E",
    ]

    try:
        completed = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired as e:
        completed = e
        timed_out = True

    # Clean up temporary files
    os.unlink(f.name)

    # Parse SPIN output
    stdout = completed.stdout if not timed_out else ""
    stderr = completed.stderr if not timed_out else ""

    # Check for different types of errors/results
    syntax_error = False
    compilation_error = False
    has_errors = False
    errors_found = 0

    if not timed_out:
        # Check for SPIN syntax errors (during spin -a)
        if "spin:" in stderr and "error" in stderr.lower():
            syntax_error = True

        # Check for compilation errors (during gcc)
        if "error:" in stderr and ("gcc" in stderr or "cc1" in stderr):
            compilation_error = True

        # Parse verification results from pan output
        # Look for: "errors: 0" or "errors: N"
        error_match = re.search(r"errors:\s+(\d+)", stdout)
        if error_match:
            errors_found = int(error_match.group(1))
            has_errors = errors_found > 0

        # Check for specific violation types
        has_deadlock = "deadlock" in stdout.lower()
        has_assertion_violation = "assertion violated" in stdout.lower()
        has_invalid_endstate = "invalid end state" in stdout.lower()
        has_ltl_violation = re.search(r"pan:.*claim.*violated", stdout) is not None

        # Detailed error information
        if has_errors or has_deadlock or has_assertion_violation or has_ltl_violation:
            has_errors = True

    # Determine success
    # Success means: no timeout, spin -a succeeded, gcc succeeded, pan found 0 errors
    succeed = (
        not timed_out
        and not syntax_error
        and not compilation_error
        and completed.returncode == 0
        and not has_errors
    )

    return {
        "out": stdout,
        "err": stderr
        if not timed_out
        else f"TimeoutExpired: command exceeded {timeout}s",
        "returncode": completed.returncode if not timed_out else -1,
        "succeed": succeed,
        "timed_out": timed_out,
        "syntax_error": syntax_error,
        "compilation_err": compilation_error,
        "verification_errors": errors_found,
        "has_errors": has_errors,
    }
