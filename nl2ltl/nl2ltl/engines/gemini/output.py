"""Parse Gemini output to produce Dict[Formula, Float] result."""

import re
from dataclasses import dataclass
from typing import Dict, Match, Set, Tuple, cast

from pylogics.syntax.base import Formula

from nl2ltl.engines.utils import _get_formulas
from nl2ltl.filters.base import Filter


@dataclass
class GeminiOutput:
    """Dataclass to represent the Gemini output."""

    pattern: str
    entities: Tuple[str, ...]

    def __post_init__(self):
        """Do consistency checks after initialization."""
        assert self.pattern is not None
        assert self.entities is not None


@dataclass
class _GeminiOutputWrapper:
    """A wrapper to the textual output of Gemini."""

    output: object

    @property
    def text(self) -> str:
        """Get the text content from Gemini response."""
        # Gemini response has a .text property
        return self.output.text

    @property
    def pattern(self) -> str:
        """Get the predicted pattern."""
        pattern_match = re.search("PATTERN: (.*)\n", self.text)
        if pattern_match is None:
            raise ValueError("Could not find PATTERN in Gemini response")
        return str(pattern_match.group(1))

    @property
    def entities(self) -> Tuple[str]:
        """Get the predicted entities."""
        entities_match = re.search("SYMBOLS: (.*)", self.text)
        if entities_match is None:
            raise ValueError("Could not find SYMBOLS in Gemini response")

        entities_str = entities_match.group(1)
        # Split by comma and strip whitespace
        return tuple(e.strip() for e in entities_str.split(",") if e.strip())


def parse_gemini_output(gemini_output: object) -> GeminiOutput:
    """
    Parse the Gemini output.

    :param gemini_output: the Gemini API response object.
    :return: a GeminiOutput instance.
    """
    wrapper = _GeminiOutputWrapper(gemini_output)
    pattern: str = wrapper.pattern
    entities: Tuple[str] = wrapper.entities
    gemini_result = GeminiOutput(pattern, entities)
    return gemini_result


def parse_gemini_result(output: GeminiOutput, filtering: Filter = None) -> Dict[Formula, float]:
    """
    Build a dict of formulas, given the GeminiOutput object.

    :param output: a GeminiOutput instance.
    :param filtering: a custom filtering function
    :return: the dictionary of formulas.
    """
    result: Dict[Formula, float] = {}
    symbols: Dict[str, float] = {e: 1 for e in output.entities}
    formulas: Set[Formula] = _get_formulas(output.pattern, symbols)

    if all(isinstance(f, Formula) for f in formulas):
        for f in formulas:
            result[f] = 1
    else:
        raise Exception("The output is not a valid formula.")

    if filtering:
        return filtering.enforce(result, symbols)
    else:
        return result
