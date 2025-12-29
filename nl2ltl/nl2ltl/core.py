"""NL2LTLf core module."""

from typing import Dict

from pylogics.syntax.base import And, Formula, Implies, Not, Or
from pylogics.syntax.ltl import Always, Atomic, Eventually  # LTL Operators

from nl2ltl.engines import Engine
from nl2ltl.filters.base import Filter


def _call_translation_method(
    utterance: str, engine: Engine, filtering: Filter, method_name: str
) -> Dict[Formula, float]:
    """Call the translation method."""
    method = getattr(engine, method_name)
    return method(utterance, filtering)


def translate(utterance: str, engine: Engine, filtering: Filter = None) -> Dict[Formula, float]:
    """
    From NL to LTLf.

    :param utterance: the natural language utterance to translate.
    :param engine: the engine to use.
    :param filtering: the filtering function to use.
    :return: the best matching LTL formulas with their confidence.
    """
    return _call_translation_method(utterance, engine, filtering, translate.__name__)


def custom_template_to_ltl(template_name: str, activities: list[str]) -> Formula:
    """
    Maps a custom DECLARE-like template name to a pylogics LTL Formula object.

    Args:
        template_name: The name of the custom constraint (e.g., "ExistenceTwo").
        activities: A list of activity names (e.g., ["slack", "email"]).

    Returns:
        A pylogics LTL Formula object.
    """
    if not activities:
        raise ValueError("Activities list cannot be empty for a template.")

    # Convert activity names into Atomic LTL propositions
    A = Atomic(activities[0])
    # Use B if needed, for templates like Response(A, B)
    B = Atomic(activities[1]) if len(activities) > 1 else None

    # --- 1. Mapping Logic: Define the LTL for your custom templates ---

    if template_name == "ExistenceTwo":
        # LTL: Eventually (A AND Eventually A)
        # ⋄(A ∧ ⋄A) - Requires activity A to happen at least twice.
        # This is the formula for the constraint you observed: ExistenceTwo(slack)

        # Eventually A
        Eventually_A = Eventually(A)

        # A AND Eventually A (Requires A now, and A again later)
        A_and_Eventually_A = And(A, Eventually_A)

        # Eventually (A AND Eventually A)
        ltl_formula = Eventually(A_and_Eventually_A)
        return ltl_formula

    elif template_name == "ResponseChain":
        # LTL: Always (A IMPLIES Next Eventually B)
        # This is a custom chain response: G (A -> X F B)
        # "Every time A occurs, B must occur eventually in the NEXT state or later."
        if B is None:
            raise ValueError("ResponseChain requires two activities.")

        Next_Eventually_B = Eventually(B)  # We use Eventually(B) as the whole subformula
        A_Implies_Next_Eventually_B = Implies(A, Next_Eventually_B)
        ltl_formula = Always(A_Implies_Next_Eventually_B)
        return ltl_formula

    elif template_name == "SimpleExistence":
        # LTL: Eventually A
        # ⋄A - Activity A must occur at least once.
        return Eventually(A)

    else:
        raise NotImplementedError(f"Template '{template_name}' is not supported yet.")
