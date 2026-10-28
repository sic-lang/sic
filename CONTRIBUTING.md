# Contributing

These guidelines only describe what no tool checks: the conventions enforced by configuration files or by the checks of pull requests are not restated, and the messages of the checks explain how to fix failures.
AI agents also follow [`AGENTS.md`](AGENTS.md).

## Principles

- Keep every decision auditable: record its rationale once, where it belongs (the RFC for a design decision, the commit message for a change), and link to it elsewhere.
- Before adopting a new approach, check how established projects solve the same problem.
- Cite the source of every claim about other work (papers, documentation, languages, projects) with a link on its name in the text, so that it can be checked.
- Keep everything consistent: file layout, naming, wording and terms.
  When a convention or a term changes, apply it everywhere it is used in the same change.
- Never choose a solution that increases debt of any kind: technical, documentation, consistency or process.
  The extra work a better solution requires is not a reason to settle for a worse one.
  When some debt cannot be avoided, make it explicit in an issue.
- Favor the default configuration of tools and widely established conventions; only deviate from them with a clear reason, documented where the deviation is made.

## Style

- Write in US English: documentation, comments, commit messages, issues and pull requests.
- In Markdown files, write one sentence per line, without wrapping lines at a fixed length, so that editing a sentence only changes its own line.
  A sentence too long to read on one line is probably too long.
- Sort alphabetically the lists whose order has no meaning.
- Start the README with one short sentence saying what the repository is, and copy it verbatim as the description of the repository on GitHub.

## Formalization

The Lean package of `theory/` gives each concept two modules: `Sic/<Concept>.lean` for its definitions and the properties the rest of the formalization uses, and `Sic/<Concept>/Validation.lean` for the checks that the definitions mean what the RFCs say.
Every file is a module of the [module system of Lean](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/), so that a module only passes on the imports it declares public: an import is private, unless the type of a public declaration mentions what it imports (`public import`).
The definitions of a concept are public and expose their bodies (`@[expose] public section`), so that the other modules compute with them, while its validation is private, and reads another validation with `import all`.
A proof only shows what its statement says, so a definition is validated against the examples of its RFC, and against its meaning when one exists.
The Lean of the repository is the evidence for what Sic claims, and its kernel checks the proofs, so a reader only has to check the definitions and the statements: keep them simple enough that a reader convinces themselves easily that they say what is meant.
A proof may take any form the kernel accepts, but explain in the file how it works when its tactics do not show it.
In the definitions and the statements, write the parentheses wherever the associativity or the precedence of an operator decides the meaning, as in the associativity `(p + q) + r = p + (q + r)` and the distributivity `p * (q + r) = (p * q) + (p * r)`.

## Pull Requests

- Pull requests are merged with a merge commit, and the commits they bring are exactly the ones that were reviewed.
  Make every commit meaningful on its own: fold the changes made during review into the relevant commits (`git commit --fixup=<commit>`, then `git rebase --autosquash`) and force-push.
- Update a pull request by rebasing it on `main`.

## Development Environment

Install [Nix](https://nixos.org/), with flakes enabled, on Linux (x86_64 or aarch64) or macOS (Apple silicon).
`nix develop` provides every tool the checks use, at the versions of the nixpkgs commit pinned by `flake.lock`.
With [direnv](https://direnv.net/), `.envrc` loads it when entering the repository, once allowed with `direnv allow` after reading it.

For VS Code, `nix run '.#setup-vscode'` writes the recommended extensions and settings to `.vscode/`, which git ignores: the files are then yours to customize.

## Checks

`nix run '.#check'` runs every check of the pull requests, and `nix run '.#check-<name>'` one of them, such as `nix run '.#check-reuse'`.

## Developer Certificate of Origin

By signing off a commit, you certify that you have the right to submit it under the license of the repository, as described by the [Developer Certificate of Origin 1.1](https://developercertificate.org/).

Trailers end the commit message, sorted alphabetically (e.g. `Co-Authored-By`, then `Signed-off-by`): write the other trailers at the end of the message, and let `git commit -s` add the sign-off after them.
