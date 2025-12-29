from nl2ltl import translate
from nl2ltl.engines.gemini.core import GeminiEngine
from nl2ltl.engines.utils import pretty

# Get LTL formulas from natural language
engine = GeminiEngine()
utterance = (
    "the withdraw system must check the account balance and the credit limit before processing a withdrawal request"
)
ltlf_formulas = translate(utterance, engine)
pretty(ltlf_formulas)
