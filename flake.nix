# Tools of the contributors and checks of the CI, pinned by flake.lock: the versions of the
# nixpkgs commit it locks.
{
  description = "Development environment of Sic";

  # The unstable branch, for a recent release of Lean; flake.lock pins its commit.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  # The RFCs that the metatheory formalizes, whose names the pages of the correspondence list:
  # flake.lock pins the commit of the branch of RFC 36 until it is merged.
  inputs.rfcs = {
    url = "github:sic-lang/rfcs/type-system";
    flake = false;
  };

  outputs =
    { nixpkgs, rfcs, ... }:
    let
      # The popular systems whose tools are all in the binary cache of nixpkgs: Linux on x86_64 and
      # aarch64, and macOS on Apple silicon.
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-linux"
      ];
      outputs = nixpkgs.lib.genAttrs systems (system: perSystem nixpkgs.legacyPackages.${system});
      perSystem =
        pkgs:
        let
          inherit (pkgs) lib;
          json = pkgs.formats.json { };
          # A command of the flake, in two variants of the same script: nix run builds the one that
          # skips ShellCheck, quickly, and nix flake check, run by the flake check, the one that runs it.
          command = args: {
            run = pkgs.writeShellApplication (args // { checkPhase = ":"; });
            checked = pkgs.writeShellApplication args;
          };
          app = program: description: {
            type = "app";
            program = lib.getExe program.run;
            meta = { inherit description; };
          };
          # The files of the RFCs at the pinned commit, to which the pages of the correspondence link.
          rfcsUrl = "https://github.com/sic-lang/rfcs/blob/${rfcs.rev}";
          # Mermaid 12, in place of the Mermaid 11.6.0 that mdbook-mermaid 0.17.1 bundles, whose layout
          # stretches the boxes of the graph of the imports far wider than their modules.
          mermaidJs = pkgs.fetchurl {
            url = "https://cdn.jsdelivr.net/npm/mermaid@12.2.0/dist/mermaid.min.js";
            hash = "sha256-qKam+AWwdKgmGiglyG+ZyAVKyzs19Qu34kpPnyw8O58=";
          };
          # The checks of the files: their tools, also provided by the development shell, and their
          # command, run from the root of the repository.
          fileChecks = {
            actionlint = {
              tools = [ pkgs.actionlint ];
              command = "actionlint";
            };
            editorconfig = {
              tools = [ pkgs.editorconfig-checker ];
              command = "editorconfig-checker";
            };
            # Runs the Nix of the environment, which builds the checked variants of the commands.
            flake = {
              tools = [ ];
              command = "nix flake check --quiet";
            };
            # Builds the Lean package of the metatheory, whose proofs the kernel of Lean checks, replays
            # its declarations in the kernel, which catches those added without checking them, and
            # checks the axioms they depend on; a warning fails it too.
            lean = {
              tools = [ pkgs.lean4 ];
              command = lib.concatStringsSep " && " [
                "lake --dir theory build --wfail"
                "lake --dir theory env leanchecker Sic SicExample"
                "lake --dir theory env lean --run theory/CheckAxioms.lean theory/Sic theory/SicExample"
              ];
            };
            # Relates the declarations of the metatheory to the names of the RFCs, which fails if one of
            # them gives a name that no RFC has.
            correspondence = {
              tools = [
                pkgs.coreutils
                pkgs.lean4
              ];
              command = lib.concatStringsSep " && " [
                "lake --dir theory build --wfail"
                "lake --dir theory env lean --run theory/Correspondence.lean ${rfcs} ${rfcsUrl} \"$(mktemp -d)\" theory/Sic theory/SicExample >/dev/null"
              ];
            };
            # Checks the imports of the modules of Sic/ against the rules of theory/imports.toml, through
            # the modules they import in turn, which fails with the path of the imports that a rule
            # forbids or does not allow.
            imports = {
              tools = [
                pkgs.coreutils
                pkgs.lean4
              ];
              command = lib.concatStringsSep " && " [
                "lake --dir theory build --wfail"
                "lake --dir theory env lean --run theory/Imports.lean theory/imports.toml \"$(mktemp)\" theory/Sic"
              ];
            };
            # Checks that every module of the metatheory imports only what it uses, and publicly only
            # what the types of its public declarations mention, with the import minimizer of Lake,
            # whose fixes `lake --dir theory shake --fix` applies; it reads every module, since the
            # libraries have no root module that imports them all.
            shake = {
              tools = [
                pkgs.findutils
                pkgs.gnused
                pkgs.lean4
              ];
              command = lib.concatStringsSep " && " [
                "lake --dir theory build --wfail"
                "git ls-files -z 'theory/Sic/*.lean' 'theory/SicExample/*.lean' | sed -z 's#^theory/##; s#\\.lean$##; s#/#.#g' | xargs -0 lake --dir theory shake"
              ];
            };
            markdownlint = {
              tools = [ pkgs.markdownlint-cli2 ];
              command = "markdownlint-cli2 '**/*.md'";
            };
            nixfmt = {
              tools = [
                pkgs.findutils
                pkgs.nixfmt
              ];
              command = "git ls-files -z '*.nix' | xargs -0 nixfmt --check";
            };
            reuse = {
              tools = [ pkgs.reuse ];
              command = "reuse lint";
            };
            shellcheck = {
              tools = [
                pkgs.findutils
                pkgs.shellcheck
              ];
              command = "git ls-files -z .envrc '*.sh' | xargs -0 shellcheck";
            };
            shfmt = {
              tools = [
                pkgs.findutils
                pkgs.shfmt
              ];
              command = "git ls-files -z .envrc '*.sh' | xargs -0 shfmt --diff";
            };
            # The files Git does not ignore, since Taplo reads no .gitignore, while Lake fetches packages
            # with TOML files.
            taplo = {
              tools = [
                pkgs.findutils
                pkgs.taplo
              ];
              command = "git ls-files -z --cached --others --exclude-standard '*.toml' | xargs -0 taplo fmt --check";
            };
            typos = {
              tools = [ pkgs.typos ];
              command = "typos";
            };
            yamllint = {
              tools = [ pkgs.yamllint ];
              command = "yamllint --strict .";
            };
          };
          # Checks the commits after a base, origin/main by default, up to a head, HEAD by default: each
          # one is signed off by its author (CONTRIBUTING.md), and a merge commit only merges the base,
          # to resolve a conflict.
          checkCommits = command {
            name = "check-commits";
            runtimeInputs = [
              pkgs.coreutils
              pkgs.git
              pkgs.gnugrep
            ];
            text = ''
              base=''${1:-origin/main}
              head=''${2:-HEAD}
              status=0
              for commit in $(git rev-list --merges "$base..$head"); do
                for parent in $(git log -1 --format='%P' "$commit" | cut -d ' ' -f 2-); do
                  if ! git merge-base --is-ancestor "$parent" "$base"; then
                    echo "$(git log -1 --format='%h %s' "$commit"): merges another branch than $base" >&2
                    status=1
                  fi
                done
              done
              for commit in $(git rev-list "$base..$head"); do
                author=$(git log -1 --format='%an <%ae>' "$commit")
                if ! git log -1 --format='%(trailers:key=Signed-off-by,valueonly)' "$commit" |
                  grep -qxF "$author"; then
                  echo "$(git log -1 --format='%h %s' "$commit"): no Signed-off-by: $author" >&2
                  status=1
                fi
              done
              exit "$status"
            '';
          };
          # Every check, as a command check-<name>: each job of the CI runs one of them, listed in the
          # matrix of .github/workflows/checks.yml, where a new check must be added too.
          checkCommands =
            lib.mapAttrs (
              name: check:
              command {
                name = "check-${name}";
                runtimeInputs = [ pkgs.git ] ++ check.tools;
                text = ''
                  cd "$(git rev-parse --show-toplevel)"
                  ${check.command}
                '';
              }
            ) fileChecks
            // {
              commits = checkCommits;
            };
          # Runs every check, and shows the output of those that fail.
          checkAll = command {
            name = "check";
            text = ''
              status=0
              run() {
                local name=$1 output
                shift
                if output=$("$@" 2>&1); then
                  echo "ok    $name"
                else
                  echo "FAIL  $name"
                  echo "$output"
                  status=1
                fi
              }
              ${lib.concatMapStrings (name: "run ${name} ${lib.getExe checkCommands.${name}.run}\n") (
                lib.attrNames checkCommands
              )}
              exit "$status"
            '';
          };
          # The recommended VS Code configuration: one extension per tool of the checks, and the one
          # that reviews the pull requests in the editor, where the Lean extension shows the proofs.
          vscodeExtensions = json.generate "extensions.json" {
            recommendations = [
              "davidanson.vscode-markdownlint"
              "editorconfig.editorconfig"
              "github.vscode-github-actions"
              "github.vscode-pull-request-github"
              "jnoortheen.nix-ide"
              "leanprover.lean4"
              "mkhl.direnv"
              "mkhl.shfmt"
              "redhat.vscode-yaml"
              "tamasfe.even-better-toml"
              "tekumara.typos-vscode"
              "timonwong.shellcheck"
            ];
          };
          vscodeSettings = json.generate "settings.json" {
            # Lines are not wrapped at a fixed length.
            "[markdown]"."editor.wordWrap" = "on";
            # The binaries of the development shell, loaded by direnv, instead of the bundled ones.
            "evenBetterToml.taplo.bundled" = false;
            "shellcheck.executablePath" = "shellcheck";
            # The nixd language server, which then formats with nixfmt instead of nix.formatterPath.
            "nix.enableLanguageServer" = true;
            "nix.serverPath" = "nixd";
            "nix.serverSettings".nixd.formatting.command = [ "nixfmt" ];
            # Lean comes from the development shell, without its version manager elan, whose absence
            # the extension would report at every start.
            "lean4.showSetupWarnings" = false;
          };
          # The recommended Git hooks: commit-msg rejects a commit without the sign-off of its author,
          # which the commits check requires, before it exists. It runs the Bash and the Git of the
          # contributor, since its copy cannot depend on paths of the Nix store, which may be collected:
          # two variants, as for the commands, the one of nix flake check runs ShellCheck.
          hook = args: {
            run = pkgs.writeTextFile (args // { executable = true; });
            checked = pkgs.writeTextFile (
              args
              // {
                executable = true;
                checkPhase = ''${lib.getExe pkgs.shellcheck} "$target"'';
              }
            );
          };
          commitMsgHook = hook {
            name = "commit-msg";
            text = ''
              #!/usr/bin/env bash
              set -euo pipefail
              author=$(git var GIT_AUTHOR_IDENT | sed 's/ [0-9]* [-+][0-9]*$//')
              if ! git interpret-trailers --parse "$1" | grep -qxF "Signed-off-by: $author"; then
                echo "no Signed-off-by: $author, which git commit -s adds" >&2
                exit 1
              fi
            '';
          };
          # A setup: writes recommended files to a directory, each under the name of its source in the
          # Nix store, without overwriting a file that differs from it, unless --force is given.
          setup =
            {
              name,
              dir,
              mode,
              sources,
            }:
            command {
              inherit name;
              runtimeInputs = [
                pkgs.coreutils
                pkgs.diffutils
                pkgs.git
              ];
              text = ''
                force=false
                case "$*" in
                "") ;;
                --force) force=true ;;
                *)
                  echo "usage: ${name} [--force]" >&2
                  exit 2
                  ;;
                esac
                dir=${dir}
                sources=(${lib.concatStringsSep " " sources})
                status=0
                for source in "''${sources[@]}"; do
                  target=$dir/''${source#*-}
                  if [ ! -e "$target" ]; then
                    install -D -m ${mode} "$source" "$target"
                    echo "created $target"
                  elif cmp -s "$source" "$target"; then
                    echo "up to date $target"
                  elif $force; then
                    install -m ${mode} "$source" "$target"
                    echo "overwritten $target"
                  else
                    diff -u --color=auto "$target" "$source" || true
                    echo "kept $target, which differs from the recommended one above: merge it by hand, or overwrite it with --force" >&2
                    status=1
                  fi
                done
                exit "$status"
              '';
            };
          # Every setup, as a command setup-<name>, with the description of its app.
          setups = {
            # Copies the hooks to the directory where Git looks for them, .git/hooks unless
            # core.hooksPath says otherwise.
            hooks = {
              description = "Copy the recommended Git hooks to the hooks of the clone";
              command = setup {
                name = "setup-hooks";
                dir = "$(git rev-parse --path-format=absolute --git-path hooks)";
                mode = "755";
                sources = [ commitMsgHook.run ];
              };
            };
            # Writes the configuration to .vscode/, which Git ignores.
            vscode = {
              description = "Write the recommended VS Code configuration to .vscode/";
              command = setup {
                name = "setup-vscode";
                dir = "$(git rev-parse --show-toplevel)/.vscode";
                mode = "644";
                sources = [
                  vscodeExtensions
                  vscodeSettings
                ];
              };
            };
          };
          # Runs every setup that the contributor confirms, since each one configures a tool they may
          # not use, with the same arguments.
          setupAll = command {
            name = "setup";
            text = ''
              status=0
              confirm() {
                local answer
                read -r -p "$1? [y/N] " answer || true
                [[ $answer == [yY]* ]]
              }
              ${lib.concatMapStrings (name: ''
                if confirm "${setups.${name}.description}"; then
                  ${lib.getExe setups.${name}.command.run} "$@" || status=1
                fi
              '') (lib.attrNames setups)}
              exit "$status"
            '';
          };
          # Generates the documentation of the metatheory with doc-gen4, in
          # theory/docbuild/.lake/build/doc: Lake fetches doc-gen4, whose libraries need a C compiler, and
          # the facet docs of the module SicDocs documents every module it imports.
          docs = command {
            name = "docs";
            runtimeInputs = [
              pkgs.coreutils
              pkgs.findutils
              pkgs.git
              pkgs.gnused
              pkgs.lean4
              pkgs.stdenv.cc
            ];
            text = ''
              cd "$(git rev-parse --show-toplevel)/theory"
              {
                find Sic SicExample -name "*.lean" | LC_ALL=C sort | sed 's|\.lean$||; s|/|.|g; s|^|import |'
                echo
                echo "/-! The modules of the metatheory, imported so that doc-gen4 documents them all. -/"
              } >docbuild/SicDocs.lean
              # doc-gen4 v4.34.1 does not write the pages again when the modules change, since its empty
              # markers hide the changes upstream of them (leanprover/doc-gen4#389, fixed in v4.35.0):
              # without the marker, it writes them again at each run, until Lean 4.35 (#41).
              rm -f docbuild/.lake/build/doc-data/SicDocs--library.docs_built*
              lake --dir docbuild build SicDocs:docs
              echo "The documentation is in $PWD/docbuild/.lake/build/doc."
            '';
          };
          # Builds into book/ the site that GitHub Pages serves: the book of the correspondence, whose
          # introduction is the README and whose pages Correspondence.lean writes into site/, and the
          # documentation of the metatheory in book/theory/.
          buildSite = command {
            name = "build-site";
            runtimeInputs = [
              pkgs.coreutils
              pkgs.git
              pkgs.lean4
              pkgs.mdbook
              pkgs.mdbook-katex
              pkgs.mdbook-mermaid
            ];
            text = ''
              cd "$(git rev-parse --show-toplevel)"
              rm -rf site book
              mkdir site
              ln -s ../README.md site/introduction.md
              ln -s ../LICENSES site/LICENSES
              lake --dir theory build --wfail
              {
                printf '[Introduction](introduction.md)\n\n'
                lake --dir theory env lean --run theory/Correspondence.lean ${rfcs} ${rfcsUrl} site theory/Sic theory/SicExample
                lake --dir theory env lean --run theory/Imports.lean theory/imports.toml site/imports.md theory/Sic
                printf -- '- [Imports](imports.md)\n'
              } >site/SUMMARY.md
              # The JavaScript files of mdbook-mermaid, which its install command writes next to the
              # book.toml it rewrites: a temporary one, which keeps that of the repository as it is.
              mermaid=$(mktemp -d)
              trap 'rm -rf "$mermaid"' EXIT
              touch "$mermaid/book.toml"
              RUST_LOG=warn mdbook-mermaid install "$mermaid"
              cp "$mermaid"/*.js .
              install -m 644 ${mermaidJs} mermaid.min.js
              mdbook build
              ${lib.getExe docs.run}
              cp -r theory/docbuild/.lake/build/doc book/theory
            '';
          };
        in
        {
          apps =
            lib.mapAttrs' (
              name: command: lib.nameValuePair "check-${name}" (app command "Run the ${name} check")
            ) checkCommands
            // {
              check = app checkAll "Run every check";
              build-site = app buildSite "Build the site that GitHub Pages serves into book/";
              docs = app docs "Generate the documentation of the metatheory";
              setup = app setupAll "Run every setup";
            }
            // lib.mapAttrs' (
              name: setup: lib.nameValuePair "setup-${name}" (app setup.command setup.description)
            ) setups;

          # Built by nix flake check, which runs ShellCheck on their scripts and on the hooks.
          checks =
            lib.mapAttrs' (name: command: lib.nameValuePair "check-${name}" command.checked) checkCommands
            // {
              build-site = buildSite.checked;
              check = checkAll.checked;
              docs = docs.checked;
              hook-commit-msg = commitMsgHook.checked;
              setup = setupAll.checked;
            }
            // lib.mapAttrs' (name: setup: lib.nameValuePair "setup-${name}" setup.command.checked) setups;

          # The tools of the checks, and the language servers of the editors.
          devShells.default = pkgs.mkShellNoCC {
            packages = lib.unique (lib.concatMap (check: check.tools) (lib.attrValues fileChecks)) ++ [
              pkgs.nixd
            ];
            # The Lean extension of VS Code requires the version of Lean in lean-toolchain, which Git
            # ignores: written from the Lean of the shell, it always matches flake.lock.
            shellHook = ''
              echo "leanprover/lean4:v${pkgs.lean4.version}" >"$(${lib.getExe pkgs.git} rev-parse --show-toplevel)/theory/lean-toolchain"
            '';
          };
        };
    in
    {
      apps = nixpkgs.lib.mapAttrs (system: outputs: outputs.apps) outputs;
      checks = nixpkgs.lib.mapAttrs (system: outputs: outputs.checks) outputs;
      devShells = nixpkgs.lib.mapAttrs (system: outputs: outputs.devShells) outputs;
    };
}
