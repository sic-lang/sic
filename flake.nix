# Tools of the contributors and checks of the CI, pinned by flake.lock: the versions of the
# nixpkgs commit it locks.
{
  description = "Development environment of Sic";

  # The unstable branch, for a recent release of Lean; flake.lock pins its commit.
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs =
    { nixpkgs, ... }:
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
                "lake --dir theory env leanchecker Sic"
                "lake --dir theory env lean --run theory/CheckAxioms.lean theory/Sic"
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
            taplo = {
              tools = [ pkgs.taplo ];
              command = "taplo fmt --check";
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
          # Checks the commits after a base, origin/main by default: each one is signed off by its
          # author (CONTRIBUTING.md), and none is a merge commit, as pull requests are rebased.
          checkCommits = command {
            name = "check-commits";
            runtimeInputs = [
              pkgs.git
              pkgs.gnugrep
            ];
            text = ''
              base=''${1:-origin/main}
              status=0
              for commit in $(git rev-list --merges "$base..HEAD"); do
                echo "$(git log -1 --format='%h %s' "$commit"): merge commit, rebase instead" >&2
                status=1
              done
              for commit in $(git rev-list --no-merges "$base..HEAD"); do
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
          # Writes the recommended configuration to .vscode/, which git ignores, without overwriting a
          # file that differs from it, unless --force is given.
          setupVscode = command {
            name = "setup-vscode";
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
                echo "usage: setup-vscode [--force]" >&2
                exit 2
                ;;
              esac
              dir=$(git rev-parse --show-toplevel)/.vscode
              status=0
              for source in ${vscodeExtensions} ${vscodeSettings}; do
                target=$dir/''${source#*-}
                if [ ! -e "$target" ]; then
                  install -D -m 644 "$source" "$target"
                  echo "created $target"
                elif cmp -s "$source" "$target"; then
                  echo "up to date $target"
                elif $force; then
                  install -m 644 "$source" "$target"
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
        in
        {
          apps =
            lib.mapAttrs' (
              name: command: lib.nameValuePair "check-${name}" (app command "Run the ${name} check")
            ) checkCommands
            // {
              check = app checkAll "Run every check";
              setup-vscode = app setupVscode "Write the recommended VS Code configuration to .vscode/";
            };

          # Built by nix flake check, which runs ShellCheck on their scripts.
          checks =
            lib.mapAttrs' (name: command: lib.nameValuePair "check-${name}" command.checked) checkCommands
            // {
              check = checkAll.checked;
              setup-vscode = setupVscode.checked;
            };

          # The tools of the checks, and the language servers of the editors.
          devShells.default = pkgs.mkShellNoCC {
            packages = lib.unique (lib.concatMap (check: check.tools) (lib.attrValues fileChecks)) ++ [
              pkgs.nixd
            ];
            # The Lean extension of VS Code requires the version of Lean in lean-toolchain, which git
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
