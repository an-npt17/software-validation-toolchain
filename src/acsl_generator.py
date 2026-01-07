"""Generate ACSL specifications from natural language using Gemini API."""

import os
import re
from typing import Final

import google.generativeai as genai

from src.types import ACSLSpecification, SystemDescription

# Configure Gemini
genai.configure(api_key=os.environ.get("GOOGLE_API_KEY"))

ACSL_SYSTEM_PROMPT: Final[str] = """You are an expert in formal verification and ACSL (ANSI/ISO C Specification Language) for Frama-C.

Your task is to convert natural language system descriptions into complete C programs with ACSL annotations.

Requirements:
1. Generate valid C code with proper ACSL annotations
2. Include function contracts (requires, ensures clauses)
3. Add loop invariants where necessary
4. Use assertions for safety properties
5. Include meaningful variable annotations
6. For concurrent systems, model using shared variables and proper synchronization
7. Demonstrate potential violations if the system has errors (e.g., race conditions, buffer overflows)

ACSL annotations to use:
- /*@ requires ...; */ - precondition
- /*@ ensures ...; */ - postcondition
- /*@ assert ...; */ - assertion
- /*@ loop invariant ...; */ - loop invariant
- /*@ assigns ...; */ - frame condition

Output format:
First, provide the complete C code with ACSL annotations between ```c and ``` tags.
Then, list each major ACSL annotation on a separate line starting with "ACSL:" followed by a description.

Example output:
```c
// Your C code with ACSL annotations here
```
ACSL: Mutex ensures exclusive access (at most one process in critical section)
ACSL: No deadlock - every request eventually gets granted
"""


class ACSLGenerator:
    """Generates C code with ACSL specifications from natural language using Gemini."""

    def __init__(self, model_name: str = "gemini-1.5-flash") -> None:
        """Initialize the ACSL generator.

        Args:
            model_name: The Gemini model to use
        """
        self.model = genai.GenerativeModel(
            model_name=model_name,
            generation_config=genai.GenerationConfig(
                temperature=0.3,
                top_p=0.95,
                max_output_tokens=8192,
            ),
        )

    def generate(self, system_desc: SystemDescription) -> ACSLSpecification:
        """Generate C code with ACSL from a system description.

        Args:
            system_desc: Natural language description of the system

        Returns:
            ACSLSpecification containing the generated code and annotations

        Raises:
            ValueError: If generation fails or output is invalid
        """
        user_prompt = self._build_user_prompt(system_desc)

        response = self.model.generate_content(
            [ACSL_SYSTEM_PROMPT, user_prompt]
        )

        if not response.text:
            raise ValueError("Empty response from Gemini API")

        return self._parse_response(response.text, system_desc.description)

    def _build_user_prompt(self, system_desc: SystemDescription) -> str:
        """Build the user prompt from the system description.

        Args:
            system_desc: System description

        Returns:
            Formatted prompt string
        """
        prompt_parts = [
            f"System type: {system_desc.system_type}",
            f"\nDescription: {system_desc.description}",
        ]

        if system_desc.expected_properties:
            props = "\n".join(f"- {prop}" for prop in system_desc.expected_properties)
            prompt_parts.append(f"\nExpected properties to verify:\n{props}")

        return "\n".join(prompt_parts)

    def _parse_response(
        self, response_text: str, description: str
    ) -> ACSLSpecification:
        """Parse the Gemini response to extract C code and ACSL annotations.

        Args:
            response_text: Raw response from Gemini
            description: Original system description

        Returns:
            Parsed ACSLSpecification

        Raises:
            ValueError: If parsing fails
        """
        # Extract C code block
        c_match = re.search(r"```c\n(.*?)```", response_text, re.DOTALL | re.IGNORECASE)
        if not c_match:
            # Try without language specifier
            c_match = re.search(r"```\n(.*?)```", response_text, re.DOTALL)

        if not c_match:
            raise ValueError("Could not find C code block in response")

        c_code = c_match.group(1).strip()

        # Extract ACSL annotation descriptions
        acsl_annotations: list[str] = []
        for line in response_text.split("\n"):
            if line.strip().startswith("ACSL:"):
                acsl_desc = line.strip()[5:].strip()
                acsl_annotations.append(acsl_desc)

        # Also extract ACSL comments from the code itself
        acsl_in_code = re.findall(r"/\*@(.*?)\*/", c_code, re.DOTALL)
        for annotation in acsl_in_code:
            cleaned = " ".join(annotation.strip().split())
            if cleaned and cleaned not in acsl_annotations:
                acsl_annotations.append(cleaned)

        return ACSLSpecification(
            c_code=c_code,
            acsl_annotations=acsl_annotations,
            description=description,
        )
