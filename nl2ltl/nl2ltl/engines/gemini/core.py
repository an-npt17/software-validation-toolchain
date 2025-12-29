"""
Implementation of the Gemini engine.

Website:

    https://ai.google.dev

"""

import json
from enum import Enum
from pathlib import Path
from typing import Dict, Set

import google.generativeai as genai
from pylogics.syntax.base import Formula

from nl2ltl.engines.base import Engine
from nl2ltl.engines.gemini import ENGINE_ROOT
from nl2ltl.engines.gemini.output import GeminiOutput, parse_gemini_output, parse_gemini_result
from nl2ltl.filters.base import Filter

try:
    # Configure with API key from environment variable
    genai.configure()
    client_available = True
except Exception:
    client_available = False

engine_root = ENGINE_ROOT
DATA_DIR = engine_root / "data"
PROMPT_PATH = engine_root / DATA_DIR / "prompt.json"


class Models(Enum):
    """The set of available Gemini language models."""

    GEMINI_PRO = "gemini-pro"
    GEMINI_15_PRO = "gemini-1.5-pro"
    GEMINI_15_FLASH = "gemini-1.5-flash"
    GEMINI_20_FLASH = "gemini-2.0-flash"
    GEMINI_25_FLASH = "gemini-2.5-flash-lite"


SUPPORTED_MODELS: Set[str] = {v.value for v in Models}


class GeminiEngine(Engine):
    """The Gemini engine."""

    def __init__(
        self,
        model: str = Models.GEMINI_25_FLASH.value,
        prompt: Path = PROMPT_PATH,
        temperature: float = 0.5,
    ):
        """Gemini LLM Engine initialization."""
        self._model = model
        self._prompt = self._load_prompt(prompt)
        self._temperature = temperature
        self._client = None

        self._check_consistency()
        self._initialize_client()

    def _load_prompt(self, prompt):
        return json.load(open(prompt))["prompt"]

    def _check_consistency(self) -> None:
        """Run consistency checks."""
        self.__check_client_available()
        self.__check_model_support()

    def __check_client_available(self):
        """Check that the Gemini client is available."""
        if not client_available:
            raise Exception(
                "Google Generative AI client not available. "
                "Please install it manually using:"
                "\n"
                "pip install google-generativeai"
                "\n"
                "And set your API key using:"
                "\n"
                "export GOOGLE_API_KEY='your-api-key'"
            )

    def __check_model_support(self):
        """Check if the model is a supported model."""
        is_supported = self.model in SUPPORTED_MODELS
        if not is_supported:
            raise Exception(f"The LLM model {self.model} is not currently supported by nl2ltl.")

    def _initialize_client(self):
        """Initialize the Gemini model client."""
        generation_config = {
            "temperature": self._temperature,
            "top_p": 1.0,
            "max_output_tokens": 200,
        }

        self._client = genai.GenerativeModel(
            model_name=self._model,
            generation_config=generation_config,
        )

    @property
    def model(self) -> str:
        """Get the Gemini model."""
        return self._model

    @property
    def prompt(self) -> str:
        """Get the Gemini prompt."""
        return self._prompt

    @property
    def temperature(self) -> float:
        """Get the Gemini temperature."""
        return self._temperature

    def translate(self, utterance: str, filtering: Filter = None) -> Dict[Formula, float]:
        """From NL to best matching LTL formulas with confidence."""
        return _process_utterance(
            utterance,
            self._client,
            self.prompt,
            self.temperature,
            filtering,
        )


def _process_utterance(
    utterance: str,
    client: genai.GenerativeModel,
    prompt: str,
    temperature: float,
    filtering: Filter,
) -> Dict[Formula, float]:
    """
    Process NL utterance.

    :param utterance: the natural language utterance
    :param client: the Gemini model client
    :param prompt: the prompt
    :param temperature: the temperature
    :param filtering: the filter used to remove formulas
    :return: a dict matching formulas to their confidence
    """
    query = f"NL: {utterance}\n"
    full_prompt = prompt + query

    # Generate response using Gemini
    response = client.generate_content(full_prompt)

    gemini_result: GeminiOutput = parse_gemini_output(response)
    matching_formulas: Dict[Formula, float] = parse_gemini_result(gemini_result, filtering)
    return matching_formulas
