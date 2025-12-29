"""
PyLogics to SPIN LTL Formula Converter

This module converts pylogics LTL formulas and DECLARE templates to SPIN model checker format.
"""

import re
from typing import Dict, Union

from pylogics.syntax.base import Formula
from pylogics.syntax.ltl import (
    Always,
    Atomic,
    Eventually,
    Next,
    Release,
    Until,
    WeakUntil,
)

# DECLARE template to LTL mappings
DECLARE_TEMPLATES = {
    # Existence templates
    "Existence": lambda a: f"<>{a}",
    "Absence": lambda a: f"[]!{a}",
    "Exactly": lambda a, n: f"<>{a}",  # Simplified - exact count needs more complex formula
    # Relation templates
    "RespondedExistence": lambda a, b: f"<>{a} -> <>{b}",
    "Response": lambda a, b: f"[]({a} -> <>{b})",
    "AlternateResponse": lambda a, b: f"[](({a} && !{b}) -> X(!{a} U {b}))",
    "ChainResponse": lambda a, b: f"[]({a} -> X{b})",
    "Precedence": lambda a, b: f"!{b} U {a}",
    "AlternatePrecedence": lambda a, b: f"(!{b} U {a}) && []({b} -> X(!{b} U {a}))",
    "ChainPrecedence": lambda a, b: f"[]({b} -> X{a})",
    "Succession": lambda a, b: f"([]({a} -> <>{b})) && (!{b} U {a})",
    "AlternateSuccession": lambda a, b: f"[](({a} && !{b}) -> X(!{a} U {b})) && []({b} -> X(!{b} U {a}))",
    "ChainSuccession": lambda a, b: f"[]({a} <-> X{b})",
    "CoExistence": lambda a, b: f"(<>{a} -> <>{b}) && (<>{b} -> <>{a})",
    # Negative templates
    "NotCoExistence": lambda a, b: f"!(<>{a} && <>{b})",
    "NotSuccession": lambda a, b: f"[]({a} -> []!{b})",
    "NotChainSuccession": lambda a, b: f"[]({a} -> !X{b})",
}


class PyLogicsToSPINConverter:
    """Converts pylogics LTL formulas and DECLARE templates to SPIN LTL syntax."""

    def __init__(self):
        self.precedence = {
            "atomic": 0,
            "not": 1,
            "next": 2,
            "eventually": 2,
            "always": 2,
            "until": 3,
            "weakuntil": 3,
            "release": 3,
            "and": 4,
            "or": 5,
            "implies": 6,
            "equivalence": 7,
        }

    def convert(self, formula: Union[Formula, str]) -> str:
        """
        Convert a pylogics Formula or DECLARE template string to SPIN LTL syntax.

        Args:
            formula: Either a pylogics Formula object or DECLARE template string

        Returns:
            String representation in SPIN LTL format
        """
        if isinstance(formula, str):
            return self._convert_declare_template(formula)
        else:
            return self._convert_recursive(formula)

    def _convert_declare_template(self, template_str: str) -> str:
        """
        Convert a DECLARE template string to SPIN LTL.

        Handles formats like:
        - "RespondedExistence slack gmail"
        - "(RespondedExistence slack gmail)"
        - "Response(a, b)"

        Args:
            template_str: DECLARE template as string

        Returns:
            SPIN LTL formula
        """
        # Remove outer parentheses if present
        template_str = template_str.strip()
        if template_str.startswith("(") and template_str.endswith(")"):
            template_str = template_str[1:-1].strip()

        # Parse template with various formats
        # Format 1: "TemplateName param1 param2"
        parts = template_str.split()
        if len(parts) >= 1:
            template_name = parts[0]
            params = parts[1:]
        else:
            return f"/* Unable to parse: {template_str} */"

        # Format 2: "TemplateName(param1, param2)"
        if "(" in template_name:
            match = re.match(r"(\w+)\((.*)\)", template_str)
            if match:
                template_name = match.group(1)
                params_str = match.group(2)
                params = [p.strip() for p in params_str.split(",")]

        # Look up the template
        if template_name in DECLARE_TEMPLATES:
            template_func = DECLARE_TEMPLATES[template_name]
            try:
                return template_func(*params)
            except TypeError:
                return f"/* Error: {template_name} expects different number of parameters */"
        else:
            return f"/* Unknown DECLARE template: {template_name} */"

    def _needs_parens(self, parent_op: str, child_op: str) -> bool:
        """Determine if parentheses are needed based on operator precedence."""
        return self.precedence.get(child_op, 99) > self.precedence.get(parent_op, 99)

    def _get_op_type(self, formula: Formula) -> str:
        """Get the operation type of a formula."""
        if isinstance(formula, Atomic):
            return "atomic"
        elif isinstance(formula, Next):
            return "next"
        elif isinstance(formula, Eventually):
            return "eventually"
        elif isinstance(formula, Always):
            return "always"
        elif isinstance(formula, Until):
            return "until"
        elif isinstance(formula, WeakUntil):
            return "weakuntil"
        elif isinstance(formula, Release):
            return "release"
        else:
            return "unknown"

    def _convert_recursive(self, formula: Formula, parent_op: str = None) -> str:
        """
        Recursively convert a pylogics formula to SPIN format.

        Args:
            formula: The formula to convert
            parent_op: The parent operation type (for precedence handling)

        Returns:
            SPIN LTL string representation
        """
        current_op = self._get_op_type(formula)

        # Atomic propositions
        if isinstance(formula, Atomic):
            return str(formula.name)

        # Unary operators

        elif isinstance(formula, Next):
            arg = self._convert_recursive(formula.argument, current_op)
            child_op = self._get_op_type(formula.argument)
            if self._needs_parens(current_op, child_op):
                arg = f"({arg})"
            return f"X {arg}"

        elif isinstance(formula, Eventually):
            arg = self._convert_recursive(formula.argument, current_op)
            child_op = self._get_op_type(formula.argument)
            if self._needs_parens(current_op, child_op):
                arg = f"({arg})"
            return f"<>{arg}"

        elif isinstance(formula, Always):
            arg = self._convert_recursive(formula.argument, current_op)
            child_op = self._get_op_type(formula.argument)
            if self._needs_parens(current_op, child_op):
                arg = f"({arg})"
            return f"[]{arg}"

        else:
            # Fallback for unknown formula types - try string conversion
            return str(formula)

    def generate_promela_ltl(self, formula: Union[Formula, str], property_name: str = "property") -> str:
        """
        Generate a complete Promela LTL property declaration.

        Args:
            formula: Either a pylogics Formula object or DECLARE template string
            property_name: Name for the LTL property

        Returns:
            Promela LTL property declaration
        """
        spin_formula = self.convert(formula)
        return f"ltl {property_name} {{ {spin_formula} }}"


def convert_nl2ltl_to_spin(formulas_dict: Dict, property_name: str = "property") -> list:
    """
    Convert nl2ltl output (dictionary of formulas/templates with scores) to SPIN format.

    Args:
        formulas_dict: Dictionary from nl2ltl translate() function
                      Keys can be pylogics Formula objects or DECLARE template strings
        property_name: Base name for LTL properties

    Returns:
        List of tuples: (promela_declaration, confidence_score, original_formula)
    """
    converter = PyLogicsToSPINConverter()
    results = []

    for idx, (formula, score) in enumerate(formulas_dict.items()):
        prop_name = f"{property_name}_{idx}" if len(formulas_dict) > 1 else property_name
        promela_decl = converter.generate_promela_ltl(formula, prop_name)
        results.append((promela_decl, score, formula))

    return results
