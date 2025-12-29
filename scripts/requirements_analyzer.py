#!/usr/bin/env python3
"""
Requirements Analyzer
Analyzes natural language requirements for:
- Ambiguity detection
- Completeness checking
- Consistency verification
- Structure extraction
- Quality metrics
"""

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass
from enum import Enum
from typing import Dict, List, Optional, Set

# Import NLP libraries
try:
    import spacy

    SPACY_AVAILABLE = True
except ImportError:
    SPACY_AVAILABLE = False
    print("Warning: spaCy not available", file=sys.stderr)

try:
    import nltk
    from nltk.tokenize import sent_tokenize, word_tokenize

    NLTK_AVAILABLE = True
except ImportError:
    NLTK_AVAILABLE = False


class RequirementType(str, Enum):
    FUNCTIONAL = "functional"
    SAFETY = "safety"
    PERFORMANCE = "performance"
    SECURITY = "security"
    USABILITY = "usability"
    RELIABILITY = "reliability"
    UNKNOWN = "unknown"


class Priority(str, Enum):
    MUST = "must"  # shall, must, required
    SHOULD = "should"  # should, recommended
    MAY = "may"  # may, optional, could


class QualityIssue(str, Enum):
    AMBIGUOUS = "ambiguous"
    INCOMPLETE = "incomplete"
    INCONSISTENT = "inconsistent"
    VAGUE = "vague"
    COMPLEX = "too_complex"
    NON_VERIFIABLE = "non_verifiable"


@dataclass
class Requirement:
    """Structured requirement with metadata"""

    id: str
    text: str
    type: RequirementType
    priority: Priority
    entities: list[str]
    actions: list[str]
    constraints: list[dict[str, any]]
    quality_issues: list[QualityIssue]
    quality_score: float
    derived_from: Optional[str] = None
    traces_to: list[str] = None

    def __post_init__(self):
        if self.traces_to is None:
            self.traces_to = []


class RequirementsAnalyzer:
    """Analyze natural language requirements"""

    # EARS (Easy Approach to Requirements Syntax) patterns
    EARS_PATTERNS = {
        "ubiquitous": r"^(The system shall|The \w+ shall)",
        "event_driven": r"^(When|If) .+ (then )?the system shall",
        "unwanted": r"^If .+ the system shall (not|prevent|avoid)",
        "state_driven": r"^(While|During) .+ the system shall",
        "optional": r"^(Where|If) .+ is provided.* the system shall",
    }

    # Weak/ambiguous words
    WEAK_WORDS = {
        "adequate",
        "appropriate",
        "as applicable",
        "as appropriate",
        "be able to",
        "be capable",
        "but not limited to",
        "etc",
        "if possible",
        "if practical",
        "normal",
        "provide for",
        "support",
        "timely",
        "various",
        "adequate",
        "reasonable",
        "user-friendly",
        "fast",
        "slow",
        "large",
        "small",
        "efficient",
    }

    # Modal verbs for priority detection
    MUST_WORDS = {"shall", "must", "will", "is required to", "are required to"}
    SHOULD_WORDS = {"should", "is recommended", "are recommended"}
    MAY_WORDS = {"may", "can", "could", "might", "optionally"}

    def __init__(self):
        if SPACY_AVAILABLE:
            try:
                self.nlp = spacy.load("en_core_web_sm")
            except:
                print("Warning: spaCy model not loaded", file=sys.stderr)
                self.nlp = None
        else:
            self.nlp = None

    def analyze_file(self, filepath: str) -> list[Requirement]:
        """Analyze requirements from a file"""
        with open(filepath, "r") as f:
            content = f.read()

        # Parse requirements (simple line-based for now)
        requirements = []
        current_type = RequirementType.UNKNOWN
        req_id = 1

        for line in content.split("\n"):
            line = line.strip()

            # Skip empty lines and comments
            if not line or line.startswith("#"):
                # Check if comment indicates section type
                if "functional" in line.lower():
                    current_type = RequirementType.FUNCTIONAL
                elif "safety" in line.lower():
                    current_type = RequirementType.SAFETY
                elif "performance" in line.lower():
                    current_type = RequirementType.PERFORMANCE
                continue

            # Check if line looks like a requirement (starts with ID or has modal verb)
            if self._looks_like_requirement(line):
                req = self.analyze_requirement(
                    text=line, req_id=f"REQ-{req_id:03d}", req_type=current_type
                )
                requirements.append(req)
                req_id += 1

        return requirements

    def _looks_like_requirement(self, text: str) -> bool:
        """Check if text looks like a requirement"""
        text_lower = text.lower()

        # Has modal verb
        if any(
            word in text_lower
            for word in self.MUST_WORDS | self.SHOULD_WORDS | self.MAY_WORDS
        ):
            return True

        # Starts with requirement ID pattern
        if re.match(r"^[A-Z]+-\d+:", text):
            return True

        # Contains action verbs
        if re.search(
            r"\b(authenticate|validate|check|verify|process|handle|store|retrieve|calculate)\b",
            text_lower,
        ):
            return True

        return False

    def analyze_requirement(
        self,
        text: str,
        req_id: str,
        req_type: RequirementType = RequirementType.UNKNOWN,
    ) -> Requirement:
        """Analyze a single requirement"""
        # Detect priority
        priority = self._detect_priority(text)

        # Extract entities and actions
        entities = self._extract_entities(text)
        actions = self._extract_actions(text)

        # Extract constraints
        constraints = self._extract_constraints(text)

        # Check quality
        quality_issues = self._check_quality(text)
        quality_score = self._calculate_quality_score(quality_issues, text)

        # Auto-detect type if unknown
        if req_type == RequirementType.UNKNOWN:
            req_type = self._detect_type(text)

        return Requirement(
            id=req_id,
            text=text,
            type=req_type,
            priority=priority,
            entities=entities,
            actions=actions,
            constraints=constraints,
            quality_issues=quality_issues,
            quality_score=quality_score,
        )

    def _detect_priority(self, text: str) -> Priority:
        """Detect requirement priority from modal verbs"""
        text_lower = text.lower()

        if any(word in text_lower for word in self.MUST_WORDS):
            return Priority.MUST
        elif any(word in text_lower for word in self.SHOULD_WORDS):
            return Priority.SHOULD
        elif any(word in text_lower for word in self.MAY_WORDS):
            return Priority.MAY

        return Priority.SHOULD  # Default

    def _detect_type(self, text: str) -> RequirementType:
        """Auto-detect requirement type from content"""
        text_lower = text.lower()

        safety_keywords = [
            "safe",
            "secure",
            "protect",
            "prevent",
            "avoid",
            "error",
            "fail",
        ]
        performance_keywords = [
            "fast",
            "speed",
            "latency",
            "throughput",
            "response time",
            "within",
        ]
        security_keywords = [
            "authenticate",
            "authorize",
            "encrypt",
            "secure",
            "access control",
        ]

        if any(kw in text_lower for kw in safety_keywords):
            return RequirementType.SAFETY
        elif any(kw in text_lower for kw in performance_keywords):
            return RequirementType.PERFORMANCE
        elif any(kw in text_lower for kw in security_keywords):
            return RequirementType.SECURITY

        return RequirementType.FUNCTIONAL

    def _extract_entities(self, text: str) -> list[str]:
        """Extract entities (nouns, noun phrases)"""
        entities = []

        if self.nlp:
            doc = self.nlp(text)
            # Extract noun chunks
            entities = [chunk.text for chunk in doc.noun_chunks]
            # Also extract named entities
            entities.extend([ent.text for ent in doc.ents])
        else:
            # Fallback: simple pattern matching
            # Extract capitalized words (likely entities)
            entities = re.findall(r"\b[A-Z][a-z]+(?:\s+[A-Z][a-z]+)*\b", text)

        return list(set(entities))  # Remove duplicates

    def _extract_actions(self, text: str) -> list[str]:
        """Extract action verbs"""
        actions = []

        if self.nlp:
            doc = self.nlp(text)
            actions = [token.lemma_ for token in doc if token.pos_ == "VERB"]
        else:
            # Fallback: common action verbs
            action_pattern = r"\b(validate|check|verify|process|handle|store|retrieve|calculate|authenticate|authorize|encrypt|decrypt|send|receive|create|delete|update|read|write)\b"
            actions = re.findall(action_pattern, text.lower())

        return list(set(actions))

    def _extract_constraints(self, text: str) -> list[dict]:
        """Extract numerical constraints and comparisons"""
        constraints = []

        # Patterns for numerical constraints
        patterns = [
            (r"less than (\d+)", "less_than"),
            (r"greater than (\d+)", "greater_than"),
            (r"at most (\d+)", "at_most"),
            (r"at least (\d+)", "at_least"),
            (r"between (\d+) and (\d+)", "between"),
            (r"within (\d+) (second|minute|millisecond|ms|s)s?", "time_limit"),
            (r"(\d+) or (more|less|fewer)", "comparison"),
            (r"not exceed (\d+)", "not_exceed"),
        ]

        for pattern, constraint_type in patterns:
            matches = re.findall(pattern, text.lower())
            for match in matches:
                constraints.append(
                    {
                        "type": constraint_type,
                        "value": match if isinstance(match, str) else list(match),
                    }
                )

        return constraints

    def _check_quality(self, text: str) -> list[QualityIssue]:
        """Check for quality issues"""
        issues = []
        text_lower = text.lower()

        # Check for weak/ambiguous words
        for weak_word in self.WEAK_WORDS:
            if weak_word in text_lower:
                issues.append(QualityIssue.AMBIGUOUS)
                break

        # Check for vagueness (no specific values)
        if not re.search(r"\d+", text):
            if any(
                word in text_lower for word in ["adequate", "sufficient", "reasonable"]
            ):
                issues.append(QualityIssue.VAGUE)

        # Check complexity (too long or nested)
        if len(text.split()) > 30:
            issues.append(QualityIssue.COMPLEX)

        # Check for multiple clauses (too complex)
        if text.count(",") > 3 or text.count("and") > 2:
            issues.append(QualityIssue.COMPLEX)

        # Check for verifiability
        if not any(word in text_lower for word in ["shall", "must", "will"]):
            issues.append(QualityIssue.NON_VERIFIABLE)

        # Check for passive voice (harder to verify)
        passive_indicators = [
            "is performed",
            "are performed",
            "is done",
            "are done",
            "is handled",
        ]
        if any(indicator in text_lower for indicator in passive_indicators):
            issues.append(QualityIssue.AMBIGUOUS)

        return list(set(issues))  # Remove duplicates

    def _calculate_quality_score(self, issues: list[QualityIssue], text: str) -> float:
        """Calculate quality score (0-1, higher is better)"""
        score = 1.0

        # Deduct points for issues
        issue_penalties = {
            QualityIssue.AMBIGUOUS: 0.2,
            QualityIssue.VAGUE: 0.15,
            QualityIssue.COMPLEX: 0.15,
            QualityIssue.NON_VERIFIABLE: 0.3,
            QualityIssue.INCOMPLETE: 0.2,
            QualityIssue.INCONSISTENT: 0.25,
        }

        for issue in issues:
            score -= issue_penalties.get(issue, 0.1)

        # Bonus for having constraints
        if re.search(r"\d+", text):
            score += 0.1

        # Bonus for using EARS patterns
        for pattern in self.EARS_PATTERNS.values():
            if re.match(pattern, text, re.IGNORECASE):
                score += 0.1
                break

        return max(0.0, min(1.0, score))

    def generate_report(self, requirements: list[Requirement]) -> dict:
        """Generate analysis report"""
        total = len(requirements)

        if total == 0:
            return {"error": "No requirements found"}

        # Count by type
        type_counts = {}
        for req in requirements:
            type_counts[req.type.value] = type_counts.get(req.type.value, 0) + 1

        # Count by priority
        priority_counts = {}
        for req in requirements:
            priority_counts[req.priority.value] = (
                priority_counts.get(req.priority.value, 0) + 1
            )

        # Quality metrics
        avg_quality = sum(req.quality_score for req in requirements) / total
        issues_count = {}
        for req in requirements:
            for issue in req.quality_issues:
                issues_count[issue.value] = issues_count.get(issue.value, 0) + 1

        # Requirements with issues
        problematic = [req for req in requirements if req.quality_score < 0.6]

        return {
            "summary": {
                "total_requirements": total,
                "average_quality_score": round(avg_quality, 2),
                "problematic_count": len(problematic),
            },
            "by_type": type_counts,
            "by_priority": priority_counts,
            "quality_issues": issues_count,
            "problematic_requirements": [
                {
                    "id": req.id,
                    "text": req.text,
                    "score": round(req.quality_score, 2),
                    "issues": [issue.value for issue in req.quality_issues],
                }
                for req in problematic
            ],
        }


def main():
    parser = argparse.ArgumentParser(
        description="Analyze natural language requirements"
    )
    parser.add_argument("input_file", help="Requirements file to analyze")
    parser.add_argument("--output", "-o", help="Output JSON file (default: stdout)")
    parser.add_argument("--report", action="store_true", help="Generate summary report")
    parser.add_argument(
        "--format", choices=["json", "text"], default="json", help="Output format"
    )

    args = parser.parse_args()

    # Analyze requirements
    analyzer = RequirementsAnalyzer()
    requirements = analyzer.analyze_file(args.input_file)

    if args.report:
        # Generate report
        report = analyzer.generate_report(requirements)
        output = report
    else:
        # Output detailed requirements
        output = {
            "requirements": [asdict(req) for req in requirements],
            "metadata": {
                "source_file": args.input_file,
                "total_count": len(requirements),
            },
        }

    # Format output
    if args.format == "json":
        output_text = json.dumps(output, indent=2)
    else:
        # Text format
        lines = []
        lines.append("=" * 60)
        lines.append("Requirements Analysis Report")
        lines.append("=" * 60)

        if args.report:
            lines.append(
                f"\nTotal Requirements: {output['summary']['total_requirements']}"
            )
            lines.append(
                f"Average Quality: {output['summary']['average_quality_score']}"
            )
            lines.append(f"Problematic: {output['summary']['problematic_count']}")
            lines.append(f"\nBy Type: {output['by_type']}")
            lines.append(f"By Priority: {output['by_priority']}")
            lines.append(f"\nQuality Issues: {output['quality_issues']}")
        else:
            for req in requirements:
                lines.append(f"\n{req.id}: {req.text}")
                lines.append(
                    f"  Type: {req.type.value}, Priority: {req.priority.value}"
                )
                lines.append(f"  Quality Score: {req.quality_score:.2f}")
                if req.quality_issues:
                    lines.append(
                        f"  Issues: {', '.join(i.value for i in req.quality_issues)}"
                    )

        output_text = "\n".join(lines)

    # Write output
    if args.output:
        with open(args.output, "w") as f:
            f.write(output_text)
        print(f"Analysis written to {args.output}", file=sys.stderr)
    else:
        print(output_text)


if __name__ == "__main__":
    main()
