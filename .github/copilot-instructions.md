# LubySequence - Lean 4 Library
A Lean 4 formalization and study of the Luby sequence, including multiple equivalent characterizations (recursive, tree-based, and iterator/state-based), supporting lemmas on natural numbers and binary representations.

ALWAYS reference these instructions first and fallback to search or bash commands only when you encounter unexpected information that does not match the info here.

## Working Effectively

### Environment Setup
- Install elan (Lean toolchain manager):
  ```bash
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
  ```
  **NEVER CANCEL**: Installation takes 3-5 minutes. Set timeout to 10+ minutes.
- Update PATH: `export PATH="$HOME/.elan/bin:$PATH"`
- Verify installation: `elan --version` and `lake --version`

### Build Process
- **CRITICAL**: Set timeout to 60+ minutes for all build commands. Build may take 30-45 minutes.
- Navigate to project root: `cd /home/runner/work/LubySequence/LubySequence`
- Update dependencies: `lake update`
  **NEVER CANCEL**: Dependency download takes 10-15 minutes due to mathlib size. Network timeouts may occur - retry if needed.
- Build the library: `lake build`
  **NEVER CANCEL**: Full build takes 30-45 minutes. Set timeout to 60+ minutes minimum.
- Build documentation: `lake build doc` (optional)
  **NEVER CANCEL**: Documentation build takes 15-20 minutes.

### Alternative Build with Nix (if available)
- Enter Nix dev shell: `nix develop`
- Run standard Lake commands: `lake update && lake build`
- The flake.nix provides elan, Lean, Lake, typst, and tinymist

### Project Structure
```
LubySequence/
├── LubySequence.lean          # Root module (imports all components)
├── LubySequence/              # Main library modules
│   ├── Basic.lean            # Core Luby sequence definitions
│   ├── Equivalence.lean      # Proofs connecting models
│   └── Utils.lean            # Supporting utilities
├── lakefile.toml             # Lake build configuration
├── lean-toolchain           # Lean version specification (v4.28.0-rc1)
├── lake-manifest.json       # Dependency lock file
├── memo.typ                 # Typst documentation
├── presen.typ               # Typst presentation
└── .github/workflows/       # CI configuration
```

## Working with Network Limitations
When network connectivity prevents downloading dependencies:
- **READ-ONLY Analysis**: You can still examine the source code structure and understand the library design
- **Code Review**: Analyze .lean files for logic, proofs, and mathematical content
- **Documentation**: Read memo.typ and presen.typ files for mathematical background
- **File Structure**: Understand module organization and dependencies from lakefile.toml
- **CI Status**: Check .github/workflows/lean_action_ci.yml to understand automated build process
- **Dependencies**: Examine lake-manifest.json to understand what would be downloaded

## Validation
- **MANUAL VALIDATION REQUIREMENT**: After making changes to .lean files, ALWAYS run `lake build` to validate compilation.
- Check syntax with: `lake env lean --check LubySequence.lean`
- Validate individual modules: `lake env lean --check LubySequence/[ModuleName].lean`
- **SCENARIO VALIDATION**: Test importing the library in a new file:
  ```lean
  import LubySequence
  #check Luby.luby_seq
  ```
- **Offline Validation**: When network prevents building:
  - Verify file structure: `ls -la LubySequence/` should show: Basic.lean, SegmentSequence.lean Equivalence.lean, Utils.lean, Size.lean, TrailingZeros.lean, and WIP.lean.
  - Check import structure: `cat LubySequence.lean` should import `Utils`, `Basic`, `SegmentSequence`, `Equivalence`, and `WIP`
  - Examine module headers for import dependencies and ensure they match file structure
  - Validate lakefile.toml syntax and dependency versions

## Common Tasks

### Working with Lean Code
- The library uses mathlib v4.28.0-rc1 - ensure compatibility when adding dependencies
- Key modules to understand:
  - `LubySequence.Basic`: Core recursive definition of Luby sequence
  - `LubySequence.Utils`: Utility functions for binary operations
- Always check imports when modifying modules - use relative imports within the library

### Documentation
- Build Typst documents: `typst compile memo.typ` and `typst compile presen.typ`
  - **Note**: Requires typst installation. Available in Nix dev shell.
- Generate API docs: `lake build doc` then view generated HTML
  - **NEVER CANCEL**: Documentation build takes 15-20 minutes
- The Nix dev shell includes typst and tinymist LSP for documentation editing
- Mathematical background: Read memo.typ for detailed algorithmic analysis
- Presentation slides: presen.typ contains visual explanations of the Luby sequence

### Troubleshooting
- **Network timeouts during `lake update` or `lake build`**: Very common due to mathlib size and GitHub connectivity. Even `lake --help` requires network access initially.
  - Retry commands multiple times if they fail with timeout errors
  - Error message: "Timeout was reached (Failed to connect to github.com port 443...)"
  - Solution: Wait and retry, or use Nix dev shell if available
- **First-time toolchain download**: `lake` or `lean` commands will download the toolchain specified in lean-toolchain
  - This can take 5-10 minutes and may timeout
  - Be patient and retry if network issues occur
- **Build failures**: Check lean-toolchain version matches lakefile.toml requirements
- **Import errors**: Verify module structure matches file system layout
- **Memory issues**: Lean builds can use significant RAM - close other applications if needed
- **CI vs Local builds**: The GitHub Actions CI may work when local builds fail due to network infrastructure differences

## CI/CD Pipeline
- GitHub Actions workflow in `.github/workflows/lean_action_ci.yml`
- Uses `leanprover/lean-action@v1` for automated builds
- Triggers on push, pull_request, and workflow_dispatch
- Build must pass before merging - always run `lake build` locally first

## Dependencies
- **mathlib**: v4.28.0-rc1 (large library, causes long download times)
- **doc-gen4**: main branch (for documentation generation)
- **Lean**: v4.28.0-rc1 (specified in lean-toolchain)
- Additional transitive dependencies via mathlib (see lake-manifest.json)

## Performance Expectations
- **Initial setup**: 5-10 minutes (elan installation + toolchain download)
- **Dependency update**: 10-15 minutes (mathlib download)
- **Full build**: 30-45 minutes (mathlib compilation dominates)
- **Incremental builds**: 1-5 minutes (local changes only)
- **Documentation build**: 15-20 minutes

**CRITICAL REMINDER**: NEVER CANCEL long-running builds. Lean builds require patience - set explicit timeouts of 60+ minutes for safety.

## Quick Reference Commands
```bash
# Essential workflow
export PATH="$HOME/.elan/bin:$PATH"
cd /home/runner/work/LubySequence/LubySequence
lake update    # 10-15 min, NEVER CANCEL
lake build     # 30-45 min, NEVER CANCEL

# Validation
lake env lean --check LubySequence.lean
lake build doc

# Documentation
typst compile memo.typ
typst compile presen.typ
```

# Documentation Style Guide for LubySequence

Purpose
- Keep documentation clear, concise, and reproducible. Make it easy for readers to understand definitions, proofs, and examples of the Luby sequence and how to build the project and docs.

Tone and Audience
- Primary audience: Lean 4 users, contributors familiar with mathlib and formalization.
- Tone: precise, neutral, and didactic. Prefer short, direct sentences. Avoid colloquialisms.

Structure and Headings
- Use descriptive headings; prefer the following ordering for each doc:
  1. Summary / Goal (one or two lines)
  2. Context (why it matters)
  3. Minimal reproducible example (commands or code)
  4. Detailed explanation or proof sketch
  5. References (files, theorems, external resources)
- Use code blocks for commands and Lean snippets. Use Typst for slides and longer formatted math content.

Formatting rules
- Use Markdown for README-level docs and short guides; use Typst (.typ) for formal documents and slides.
- documentation in Lean files starts with "/--" and ends with "-/".
- Use Markdown for documentation in Lean files.
- Inline code: `lake build`, `#check Luby.luby_seq`
- Code blocks: annotate with the language where applicable (bash, lean, typst).
- Math: prefer Lean code for theorem statements and examples. Keep informal math in Typst or Markdown math where needed. Put spaces around all mathematical operators.

Lean / Mathlib conventions
- When referencing lemmas or definitions, link to the file and the symbol (e.g., LubySequence.Basic.luby_seq).
- Include "how to check" snippets:
  - lake env lean --check LubySequence/Basic.lean
  - #check Luby.luby_seq

Examples
- Short good example (command + expected short result):
  ```bash
  lake env lean --run - <<EOF
  import LubySequence
  #eval Luby.luby_seq 10
  EOF
  ```
  (Explain expected output in one sentence.)

Commit messages for docs
- Use "docs:" prefix for documentation-only changes, e.g. `docs: add documentation style guide`
- Mention whether the change requires a rebuild of docs (`lake build doc`) in the PR description.

How to add or update docs
- Update docs/DOCUMENTATION_STYLE.md for style changes.
- For Typst docs, add built outputs to CI doc step, but do not commit build artifacts.
- Run `typst compile memo.typ` locally in the Nix shell or the environment used for docs editing.

Linking and discoverability
- Add a one-line pointer in README.md or .github/copilot-instructions.md:
  - "Documentation style: see docs/DOCUMENTATION_STYLE.md"

Short checklist for PRs touching docs
- [ ] Proofread for precision and clarity
- [ ] Include minimal reproducible example if introducing new commands or APIs
- [ ] Run `lake build doc` when feasible (CI will also check)

Contact / Questions
- If unsure about phrasing mathematical explanations, open an issue and tag it `documentation` so reviewers can suggest clearer statements.
