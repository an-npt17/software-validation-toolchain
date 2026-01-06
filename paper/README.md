# Paper: AI-Powered Formal Verification Toolchain

This directory contains the LaTeX source for the capstone project report documenting the software validation toolchain.

## Document Structure

The paper is organized as a capstone project report using the `report` document class with the following structure:

```
paper/
├── main.tex              # Main document file with preamble and front matter
├── reference.bib         # Bibliography file with all references
├── Makefile             # Build automation
├── README.md            # This file
└── sections/            # Individual chapter files
    ├── introduction.tex     # Chapter 1: Introduction
    ├── related_work.tex     # Chapter 2: Related Work
    ├── architecture.tex     # Chapter 3: System Architecture
    ├── implementation.tex   # Chapter 4: Implementation
    ├── evaluation.tex       # Chapter 5: Evaluation
    ├── future_work.tex      # Chapter 6: Future Work
    └── conclusion.tex       # Chapter 7: Conclusion
```

## Building the Paper

### Prerequisites

You need a LaTeX distribution installed:

- **Linux**: `sudo apt install texlive-full` or use the nix environment
- **macOS**: Install MacTeX
- **Windows**: Install MiKTeX

### Build Commands

```bash
# Build the PDF (runs LaTeX + BibTeX multiple times)
make

# Quick build (single pass, no bibliography)
make quick

# View the PDF
make view

# Clean build artifacts
make clean
```

## Paper Structure

The capstone project report includes:

### Front Matter
- **Title Page**: Project title, author, supervisor, university information
- **Abstract**: Brief summary of the project and its contributions
- **Acknowledgments**: Thank advisors, funding sources, collaborators
- **Table of Contents**: Auto-generated from chapters
- **List of Figures**: Auto-generated
- **List of Tables**: Auto-generated

### Main Content (7 Chapters)

1. **Introduction**: Motivation, challenges, and overview of the toolchain
2. **Related Work**: Comparison with existing verification tools and AI-powered specification methods
3. **System Architecture**: Five-level verification pipeline design with AI integration
4. **Implementation**: Technical details of each component, tools used
5. **Evaluation**: Benchmark results, case studies, performance analysis
6. **Future Work**: Planned improvements and research directions
7. **Conclusion**: Summary of contributions and impact

### Back Matter
- **Bibliography**: Auto-generated from reference.bib
- **Appendices**: Installation guide, user guide, additional documentation

## Sections to Complete

The paper contains several `TO COMPLETE` markers indicating sections where you need to add specific information:

### 1. Title Page Information (main.tex)

Update the title page with:
- Your name and student ID
- Your email address
- Your advisor's name
- Your university and department name
- Correct submission date

### 2. Acknowledgments (main.tex)

Complete the acknowledgments section with:
- Thanks to your advisor/supervisor
- Funding sources (if any)
- Collaborators, peers, or reviewers
- Family and friends (optional)

### 3. Experimental Setup (sections/evaluation.tex)

You should provide:

- Hardware specifications (CPU, RAM)
- Operating system version
- Timeout settings used
- Number of parallel jobs
- Total runtime for full benchmark suite

Example:

```latex
Experiments were conducted on:
\begin{itemize}
    \item CPU: Intel Core i7-9700K @ 3.6GHz (8 cores)
    \item RAM: 32GB DDR4
    \item OS: NixOS 23.11
    \item Timeout: 60s per tool per benchmark
    \item Parallel jobs: 4
\end{itemize}
```

### 3. AI Translation Accuracy (sections/evaluation.tex)

You should evaluate the nl-to-acsl tool:

```bash
# Test the AI translation
cd ..
nix develop

# Create test requirements
cat > test_requirements.txt <<EOF
Buffer must not overflow
Pointer must not be null
Array index must be within bounds
Return value must be positive
Division by zero must be prevented
EOF

# Test each requirement
while IFS= read -r req; do
    echo "Testing: $req"
    uv run scripts/llm_to_acsl.py "$req" --format json
done < test_requirements.txt > paper/ai_results.json
```

Then manually review the generated ACSL for correctness and report:

- Total test cases: X
- Correct translations: Y
- Accuracy: Y/X * 100%
- Average confidence score
- Examples of correct and incorrect translations

### 4. Case Study (sections/evaluation.tex)

Document the banking system verification:

```bash
# Verify the banking system
cd ..
make verify-all TARGET=src/banking_system.c

# Document:
# - What the code does
# - Requirements identified
# - ACSL specifications written/generated
# - Verification results from Frama-C, CBMC
# - Bugs found (if any)
# - Time taken
# - Proof statistics
```

### 5. Comparison with Related Work (sections/evaluation.tex)

Compare with other tools:

- SeaHorn: SMT-based verification
- Ultimate Automizer: Software model checking
- CPAchecker: Configurable program analysis
- VeriFast: Separation logic verifier

Discuss:

- What makes your toolchain different?
- What are the advantages of multi-tool approach?
- When would you use this vs. other tools?

### 6. Adding Figures

To add the architecture diagram or other figures:

1. Export diagrams from docs/diagrams/ or create new ones

1. Place in a `figures/` subdirectory:

   ```bash
   mkdir -p figures
   cp ../docs/diagrams/system-architecture-1.svg figures/
   # Convert SVG to PDF if needed:
   inkscape figures/system-architecture-1.svg --export-pdf=figures/architecture.pdf
   ```

1. Uncomment and update the figure in the LaTeX:

   ```latex
   \begin{figure}[htbp]
   \centerline{\includegraphics[width=\columnwidth]{figures/architecture.pdf}}
   \caption{Five-level verification pipeline architecture}
   \label{fig:architecture}
   \end{figure}
   ```

## Adding Tables and Results

To add benchmark results as a table:

1. Convert results to LaTeX table format:

   ```bash
   python3 ../scripts/results_to_latex.py ../results/benchmark-run/results.json > tables/benchmark_results.tex
   ```

1. Include in paper:

   ```latex
   \input{tables/benchmark_results}
   ```

## Tips for Writing

1. **Be Specific**: Use concrete numbers and examples rather than vague statements
1. **Show Data**: Include tables and graphs for all experimental results
1. **Cite Sources**: Add proper citations for all tools and related work
1. **Proofread**: Run spell check and grammar check
1. **Consistent Terminology**: Use the same terms throughout (e.g., "toolchain" not "framework" in one place and "toolchain" in another)

## Common LaTeX Issues

### Bibliography Not Showing

Run the full build sequence:

```bash
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

### Missing Packages

Install additional LaTeX packages:

```bash
# Ubuntu/Debian
sudo apt install texlive-latex-extra texlive-science

# Or use texlive-full for everything
```

### Figures Not Displaying

- Check file paths are correct
- Ensure graphics format is supported (PDF, PNG, JPG)
- Use `\graphicspath{{figures/}}` to set search path

## Generating Final Version

Before submission:

1. Complete all "TO COMPLETE" sections
1. Add all figures and tables
1. Proofread carefully
1. Check bibliography formatting
1. Verify page limits (if applicable)
1. Run final build:
   ```bash
   make clean
   make
   ```

## Resources

- **IEEEtran Documentation**: https://www.ctan.org/pkg/ieeetran
- **LaTeX Wikibook**: https://en.wikibooks.org/wiki/LaTeX
- **Tables Generator**: https://www.tablesgenerator.com/
- **Overleaf**: Consider using Overleaf for collaborative editing

## Questions?

If you encounter issues:

1. Check the LaTeX error messages in the .log file
1. Search for the error message online
1. Consult LaTeX documentation
1. Use LaTeX StackExchange: https://tex.stackexchange.com/
