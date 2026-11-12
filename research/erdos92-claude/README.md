# Erdős 92 reductions: unverified research candidates

Three independent Claude CLI sessions generated the attempts recorded in attempts/. Claude had no command-execution tools. The graph and analytic candidates are compiled in isolated GitHub Actions; the interface candidate is preserved as an attempt and is not yet part of CI because it requires the upstream Formal Conjectures environment.

The candidates are supporting lemmas, not a proof of Erdős 92. The construction and source-fidelity review remain open. No claim is made that any candidate compiles until its exact commit passes CI. Existing results must be linked, not copied.

Source statement: [Formal Conjectures, Erdős 92](https://github.com/google-deepmind/formal-conjectures/blob/04937a4cccadd0a205abdf2c706938c6c95e4177/FormalConjectures/ErdosProblems/92.lean). Mathematical motivation: [OpenAI unit-distance paper](https://cdn.openai.com/pdf/74c24085-19b0-4534-9c90-465b8e29ad73/unit-distance-proof.pdf), Theorem 1.1. The source theorem is not redefined here.

The independent CI environment pins Lean 4.35.0, Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, and a container image digest. Reproduce the steps in .github/workflows/erdos92-claude.yml on an isolated Linux host; compilation is offline in the container. Candidate declarations print their axiom dependencies. A successful build and axiom output do not establish fidelity.
