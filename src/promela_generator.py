"""Generate Promela models from natural language using Gemini API."""

import os
import re
from typing import Final

import google.generativeai as genai

from src.types import PromelaModel, SystemDescription

# Configure Gemini
genai.configure(api_key=os.environ.get("GOOGLE_API_KEY"))

PROMELA_SYSTEM_PROMPT: Final[str] = """You are an expert in formal verification and Promela modeling for the SPIN model checker.

Your task is to convert natural language system descriptions into complete, syntactically correct Promela models with LTL properties.

Requirements:
1. Generate valid Promela syntax
2. Include all necessary process definitions
3. Add meaningful LTL properties to verify
4. Use proper synchronization primitives (channels, semaphores, atomic blocks)
5. Add comments explaining the model
6. For concurrent systems, model all possible interleavings
7. For mutex problems, demonstrate potential race conditions or deadlocks

Output format:
First, provide the Promela model code between ```promela and ``` tags.
Then, provide each LTL property on a separate line starting with "LTL:" followed by the property.

Example output:
```promela
// Your Promela code here
```
LTL: []<> (critical_section_count <= 1)
LTL: [](request -> <> grant)
"""


class PromelaGenerator:
    """Generates Promela models from natural language descriptions using Gemini."""

    def __init__(self, model_name: str = "gemini-1.5-flash") -> None:
        """Initialize the Promela generator.

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

    def generate(self, system_desc: SystemDescription) -> PromelaModel:
        """Generate a Promela model from a system description.

        Args:
            system_desc: Natural language description of the system

        Returns:
            PromelaModel containing the generated code and properties

        Raises:
            ValueError: If generation fails or output is invalid
        """
        user_prompt = self._build_user_prompt(system_desc)

        response = self.model.generate_content(
            [PROMELA_SYSTEM_PROMPT, user_prompt]
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

    def _parse_response(self, response_text: str, description: str) -> PromelaModel:
        """Parse the Gemini response to extract Promela code and LTL properties.

        Args:
            response_text: Raw response from Gemini
            description: Original system description

        Returns:
            Parsed PromelaModel

        Raises:
            ValueError: If parsing fails
        """
        # Extract Promela code block
        promela_match = re.search(
            r"```promela\n(.*?)```", response_text, re.DOTALL | re.IGNORECASE
        )
        if not promela_match:
            # Try without language specifier
            promela_match = re.search(r"```\n(.*?)```", response_text, re.DOTALL)

        if not promela_match:
            raise ValueError("Could not find Promela code block in response")

        promela_code = promela_match.group(1).strip()

        # Extract LTL properties
        ltl_properties: list[str] = []
        for line in response_text.split("\n"):
            if line.strip().startswith("LTL:"):
                ltl_prop = line.strip()[4:].strip()
                ltl_properties.append(ltl_prop)

        if not ltl_properties:
            # Try to find ltl declarations in the code itself
            ltl_in_code = re.findall(
                r"ltl\s+\w+\s*\{([^}]+)\}", promela_code, re.IGNORECASE
            )
            ltl_properties.extend(prop.strip() for prop in ltl_in_code)

        return PromelaModel(
            source_code=promela_code,
            ltl_properties=ltl_properties,
            description=description,
        )
