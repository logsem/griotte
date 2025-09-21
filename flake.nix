# Adapted from https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev/-/blob/main/flake.nix

{
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  };

  outputs = {
    self,
    flake-utils,
    nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      ocamlFlambda = _: prev: rec {
        # NOTE: Using OCaml 4.14 due to Rocq being slow with OCaml 5+
        # See: https://github.com/NixOS/nixpkgs/blob/nixos-25.05/pkgs/applications/science/logic/rocq-core/default.nix#L15
        ocamlPackages = prev.ocaml-ng.ocamlPackages_4_14.overrideScope (final: prev: {
          ocaml = prev.ocaml.override {
            flambdaSupport = true;
          };

          # NOTE: Remove this when `dune` will handle `rocq` subcommands
          # See: https://github.com/ocaml/dune/issues/11572
          dune_3 = prev.dune_3.overrideAttrs (prev: {
            nativeBuildInputs = prev.nativeBuildInputs ++ [pkgs.makeWrapper];

            postFixup = let
              coqSubcommand = newCmd: oldCmd:
                pkgs.writeScriptBin oldCmd ''
                  #!/bin/sh
                  unset COQPATH
                  rocq ${newCmd} "$@"
                '';

              coqc = coqSubcommand "compile" "coqc";
              coqdep = coqSubcommand "dep" "coqdep";
              coqpp = coqSubcommand "pp-mlg" "coqpp";
            in ''
              wrapProgram $out/bin/dune \
                --prefix PATH ":" "${pkgs.lib.makeBinPath [coqc coqdep coqpp]}" \
                --prefix OCAMLPATH ":" "${pkgs.lib.makeBinPath [coqc coqdep coqpp]}" \
                --run "export COQPATH=\$(eval echo \$ROCQPATH)"
            '';
          });
        });

        rocqPackages = prev.rocqPackages.overrideScope (_: prev: {
          rocq-core = prev.rocq-core.override {
            customOCamlPackages = ocamlPackages;
          };
        });
      };

      overlays = [ocamlFlambda ];
      pkgs = import nixpkgs {inherit overlays system;};

      name = "griotte";
      version = "0.0.0";

      meta = with pkgs.lib; {
        description = "Griotte, Rocq mechanization of a CHERIoT and principles to reason about compartmentalisation";
        homepage = "https://github.com/logsem/griotte";
        license = licenses.bsd3;
      };

      ocaml = {
        pkgs = pkgs.ocamlPackages;
        version = pkgs.ocaml.version;
      };

      rocq = {
        pkgs = pkgs.rocqPackages;
        toolchain = [rocq.pkgs.rocq-core] ++ rocq.pkgs.rocq-core.nativeBuildInputs;

        version = rocq.pkgs.rocq-core.rocq-version;

        stdpp = {
          version = "1.12.0";
          sha256 = "sha256-2o8YMkKbXrKHwtfpkdAovxl+2NZZk958GjSSd9wcEIU=";
        };

        iris = {
          version = "4.4.0";
          sha256 = "sha256-zpuaIdH2ScOuZB0Vt1TEHAbsmcT1DyoDsJpftT1M7qw=";
        };
      };

    in rec {
      packages = let
        mkDepRocqDerivation = pin: {
          pname,
          propagatedBuildInputs ? [rocq.pkgs.stdlib],
          owner ? "iris",
        }:
          rocq.pkgs.mkRocqDerivation {
            inherit pname propagatedBuildInputs owner;

            domain = "gitlab.mpi-sws.org";
            # NOTE: Remove `sed` line when Makefiles will be updated upstream
            preBuild = ''
              sed -i -e 's/"$(COQBIN)coq_makefile"/"$(COQBIN)rocq" makefile/g' Makefile
              patchShebangs coq-lint.sh
            '';

            release.${pin.version}.sha256 = "${pin.sha256}";
            version = pin.version;
          };
      in {
        theories = let
          # NOTE: Remove `coq-record-update` and `equations` when available in Nix's `RocqPackages`
          equations = rocq.pkgs.mkRocqDerivation {
            pname = "equations";
            owner = "mattam82";
            repo = "Coq-Equations";
            opam-name = "rocq-equations";

            propagatedBuildInputs = [rocq.pkgs.stdlib ocaml.pkgs.ppx_optcomp];

            mlPlugin = true;
            useDune = true;

            version = "2ce6d98dd03979369d739ac139db4da4f7eab352";
            release = {
              "2ce6d98dd03979369d739ac139db4da4f7eab352".sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
            };
          };

          stdpp = mkDepRocqDerivation rocq.stdpp {
            pname = "stdpp";
          };

          iris = mkDepRocqDerivation rocq.iris {
            pname = "iris";

            propagatedBuildInputs = [stdpp];
          };

        in
          rocq.pkgs.mkRocqDerivation {
            inherit meta version;

            pname = name;
            opam-name = name;
            src = ./theories;

            propagatedBuildInputs = [equations iris];

            preBuild = "dune() { command dune $@ --display=short; }";
            useDune = true;
          };
      };

      devShells.default = pkgs.mkShell (with packages; {
        inputsFrom = with packages; [theories];
      });

    });
}
