#!/usr/bin/env python3
"""
LLM to ACSL Converter
Converts natural language requirements to ACSL specifications using LLMs
"""

import argparse
import json
import sys
from dataclasses import dataclass
from enum import Enum
from typing import Optional

try:
    import google.generativeai as genai

    GOOGLE_AVAILABLE = True
except ImportError:
    GOOGLE_AVAILABLE = False
    print("Warning: google-generativeai not available", file=sys.stderr)

try:
    import instructor
    from pydantic import BaseModel, Field

    INSTRUCTOR_AVAILABLE = True
except ImportError:
    INSTRUCTOR_AVAILABLE = False


class RequirementType(str, Enum):
    MEMORY_SAFETY = "memory_safety"
    BOUNDS_CHECK = "bounds_check"
    NULL_SAFETY = "null_safety"
    FUNCTIONAL = "functional_correctness"
    CONCURRENCY = "concurrency"
    OVERFLOW = "overflow_check"


@dataclass
class FormalRequirement:
    """Structured formal requirement"""

    requirement_id: str
    natural_language: str
    property_type: RequirementType
    acsl_precondition: Optional[str] = None
    acsl_postcondition: Optional[str] = None
    acsl_assertion: Optional[str] = None
    applies_to_function: Optional[str] = None
    confidence: float = 0.0


# Pydantic models for structured output (if instructor available)
if INSTRUCTOR_AVAILABLE:

    class ACSLSpec(BaseModel):
        """ACSL specification from LLM"""

        requirement_type: str = Field(description="Type of requirement")
        natural_language: str = Field(description="Original NL requirement")
        precondition: Optional[str] = Field(
            default=None, description="ACSL precondition (requires clause)"
        )
        postcondition: Optional[str] = Field(
            default=None, description="ACSL postcondition (ensures clause)"
        )
        assertion: Optional[str] = Field(default=None, description="ACSL assertion")
        function_name: Optional[str] = Field(
            default=None, description="Function this applies to"
        )
        confidence: float = Field(default=0.8, description="Confidence score 0-1")


ACSL_PROMPT_TEMPLATE = """You are a formal verification expert specializing in ACSL (ANSI/ISO C Specification Language).

Convert the following natural language requirement into valid ACSL specifications.

Requirement: "{requirement}"

Context (if provided):
- Function: {function_name}
- Variables: {variables}

Return ONLY valid JSON in this exact format:
{{
  "requirement_type": "memory_safety|bounds_check|null_safety|functional_correctness|overflow_check",
  "natural_language": "original requirement",
  "precondition": "/*@ requires ... */  (or null)",
  "postcondition": "/*@ ensures ... */  (or null)",
  "assertion": "/*@ assert ... */  (or null)",
  "function_name": "function_name (or null)",
  "confidence": 0.95
}}

ACSL Guidelines:
- Use \\valid(ptr) for pointer validity
- Use \\valid(ptr+(0..n-1)) for array validity
- Use \\null for null pointers
- Use \\forall and \\exists for quantifiers
- Use \\old(x) for postconditions referring to pre-state
- Use \\result for return value in postconditions

Examples:
1. "Buffer must not overflow" → 
   "precondition": "/*@ requires \\valid(buffer+(0..size-1)); */"

2. "Pointer must not be null" →
   "precondition": "/*@ requires ptr != \\null; */"

3. "Function returns positive value" →
   "postcondition": "/*@ ensures \\result > 0; */"

Now convert the requirement above.
"""


def convert_nl_to_acsl_anthropic(
    requirement: str,
    function_name: Optional[str] = None,
    variables: Optional[list[str]] = None,
    api_key: Optional[str] = None,
) -> FormalRequirement:
    """Convert using Anthropic Claude"""
    if not ANTHROPIC_AVAILABLE:
        return mock_conversion(requirement, function_name)

    client = Anthropic(api_key=api_key)

    prompt = ACSL_PROMPT_TEMPLATE.format(
        requirement=requirement,
        function_name=function_name or "unknown",
        variables=", ".join(variables) if variables else "unknown",
    )

    message = client.messages.create(
        model="claude-sonnet-4-20250514",
        max_tokens=1024,
        messages=[{"role": "user", "content": prompt}],
    )

    # Parse JSON response
    response_text = message.content[0].text
    # Strip markdown code blocks if present
    response_text = response_text.strip()
    if response_text.startswith("```json"):
        response_text = response_text[7:]
    if response_text.startswith("```"):
        response_text = response_text[3:]
    if response_text.endswith("```"):
        response_text = response_text[:-3]

    data = json.loads(response_text.strip())

    return FormalRequirement(
        requirement_id=f"req_{hash(requirement) % 10000}",
        natural_language=requirement,
        property_type=RequirementType(
            data.get("requirement_type", "functional_correctness")
        ),
        acsl_precondition=data.get("precondition"),
        acsl_postcondition=data.get("postcondition"),
        acsl_assertion=data.get("assertion"),
        applies_to_function=data.get("function_name"),
        confidence=data.get("confidence", 0.8),
    )


def convert_nl_to_acsl_google(
    requirement: str,
    function_name: Optional[str] = None,
    variables: Optional[list[str]] = None,
    api_key: Optional[str] = None,
) -> FormalRequirement:
    """Convert using Google Gemini"""
    if not GOOGLE_AVAILABLE:
        return mock_conversion(requirement, function_name)

    genai.configure(api_key=api_key)
    model = genai.GenerativeModel("gemini-2.5-flash")

    prompt = ACSL_PROMPT_TEMPLATE.format(
        requirement=requirement,
        function_name=function_name or "unknown",
        variables=", ".join(variables) if variables else "unknown",
    )

    response = model.generate_content(prompt)
    response_text = response.text.strip()

    # Strip markdown code blocks if present
    if response_text.startswith("```json"):
        response_text = response_text[7:]
    if response_text.startswith("```"):
        response_text = response_text[3:]
    if response_text.endswith("```"):
        response_text = response_text[:-3]

    data = json.loads(response_text.strip())

    return FormalRequirement(
        requirement_id=f"req_{hash(requirement) % 10000}",
        natural_language=requirement,
        property_type=RequirementType(
            data.get("requirement_type", "functional_correctness")
        ),
        acsl_precondition=data.get("precondition"),
        acsl_postcondition=data.get("postcondition"),
        acsl_assertion=data.get("assertion"),
        applies_to_function=data.get("function_name"),
        confidence=data.get("confidence", 0.8),
    )


def mock_conversion(
    requirement: str, function_name: Optional[str] = None
) -> FormalRequirement:
    """Mock converter for testing without API keys"""
    # Simple pattern matching
    req_lower = requirement.lower()

    if "buffer" in req_lower and "overflow" in req_lower:
        return FormalRequirement(
            requirement_id=f"req_{hash(requirement) % 10000}",
            natural_language=requirement,
            property_type=RequirementType.MEMORY_SAFETY,
            acsl_precondition="/*@ requires \\valid(buffer+(0..size-1)); */",
            applies_to_function=function_name,
            confidence=0.7,
        )
    elif "null" in req_lower and "pointer" in req_lower:
        return FormalRequirement(
            requirement_id=f"req_{hash(requirement) % 10000}",
            natural_language=requirement,
            property_type=RequirementType.NULL_SAFETY,
            acsl_precondition="/*@ requires ptr != \\null; */",
            applies_to_function=function_name,
            confidence=0.8,
        )
    elif "bounds" in req_lower or "index" in req_lower:
        return FormalRequirement(
            requirement_id=f"req_{hash(requirement) % 10000}",
            natural_language=requirement,
            property_type=RequirementType.BOUNDS_CHECK,
            acsl_precondition="/*@ requires 0 <= index < size; */",
            applies_to_function=function_name,
            confidence=0.75,
        )
    else:
        return FormalRequirement(
            requirement_id=f"req_{hash(requirement) % 10000}",
            natural_language=requirement,
            property_type=RequirementType.FUNCTIONAL,
            acsl_precondition="/*@ requires true; */",
            applies_to_function=function_name,
            confidence=0.5,
        )


def format_acsl_output(req: FormalRequirement) -> str:
    """Format ACSL for insertion into C code"""
    lines = []
    lines.append(f"// Requirement: {req.natural_language}")
    lines.append(f"// Type: {req.property_type.value}")
    lines.append(f"// Confidence: {req.confidence:.2f}")

    if req.applies_to_function:
        lines.append(f"// Applies to: {req.applies_to_function}")

    lines.append("")

    if req.acsl_precondition:
        lines.append(req.acsl_precondition)

    if req.acsl_postcondition:
        lines.append(req.acsl_postcondition)

    if req.acsl_assertion:
        lines.append(req.acsl_assertion)

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Convert natural language requirements to ACSL specifications"
    )
    parser.add_argument(
        "requirement", type=str, help="Natural language requirement to convert"
    )
    parser.add_argument(
        "--function", type=str, help="Function name this requirement applies to"
    )
    parser.add_argument(
        "--variables", type=str, help="Comma-separated list of relevant variables"
    )
    parser.add_argument(
        "--provider",
        choices=["anthropic", "openai", "google", "mock"],
        default="google",
        help="LLM provider to use (default: google)",
    )
    parser.add_argument(
        "--api-key",
        type=str,
        help="API key for LLM provider (or set GOOGLE_API_KEY/ANTHROPIC_API_KEY/OPENAI_API_KEY env var)",
    )
    parser.add_argument("--output", type=str, help="Output file (default: stdout)")
    parser.add_argument(
        "--format", choices=["acsl", "json"], default="acsl", help="Output format"
    )

    args = parser.parse_args()

    # Parse variables
    variables = args.variables.split(",") if args.variables else None

    # Convert based on provider
    if args.provider == "google" and GOOGLE_AVAILABLE:
        req = convert_nl_to_acsl_google(
            args.requirement, args.function, variables, args.api_key
        )
    else:
        req = mock_conversion(args.requirement, args.function)

    # Format output
    if args.format == "json":
        output = json.dumps(
            {
                "requirement_id": req.requirement_id,
                "natural_language": req.natural_language,
                "type": req.property_type.value,
                "precondition": req.acsl_precondition,
                "postcondition": req.acsl_postcondition,
                "assertion": req.acsl_assertion,
                "function": req.applies_to_function,
                "confidence": req.confidence,
            },
            indent=2,
        )
    else:
        output = format_acsl_output(req)

    # Write output
    if args.output:
        with open(args.output, "w") as f:
            f.write(output)
        print(f"ACSL written to {args.output}", file=sys.stderr)
    else:
        print(output)


if __name__ == "__main__":
    main()
