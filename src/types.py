"""Type definitions for the verification pipeline."""

from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Literal


class VerificationTool(str, Enum):
    """Available verification tools."""

    SPIN = "spin"
    FRAMAC = "frama-c"


class VerificationStatus(str, Enum):
    """Verification result status."""

    SUCCESS = "success"
    FAILURE = "failure"
    ERROR = "error"
    TIMEOUT = "timeout"


@dataclass(frozen=True)
class VerificationResult:
    """Result of running a verification tool."""

    tool: VerificationTool
    status: VerificationStatus
    model_path: Path
    output: str
    errors: list[str]
    warnings: list[str]
    properties_checked: int
    properties_verified: int
    execution_time: float


@dataclass(frozen=True)
class PromelaModel:
    """A Promela model for SPIN verification."""

    source_code: str
    ltl_properties: list[str]
    description: str


@dataclass(frozen=True)
class ACSLSpecification:
    """An ACSL specification for Frama-C verification."""

    c_code: str
    acsl_annotations: list[str]
    description: str


@dataclass(frozen=True)
class SystemDescription:
    """Natural language description of a system to verify.

    The system_type can be any string - the verification toolchain will handle
    validation and interpretation of the type during verification.
    """

    description: str
    system_type: str  # Accept any system type - let toolchain validate
    expected_properties: list[str]
