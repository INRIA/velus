# [nix](https://nixos.org/) is a package manager for Linux and other Unix
# systems that makes package management reliable and reproducible.
#
# To compile Velus using nix, you can run the command `nix build` at the root
# of the project directory. To update nixpkgs to the latest version, you can
# run the command `nix flake update`.
{
  # Inputs of the project: where to pull the packages
  inputs = {
    # Main repo of packages for the nix package manager
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    # Core of a distributed framework for writing nix flakes for several archs
    flake-parts.url = "github:hercules-ci/flake-parts";
  };

  # Outputs of the project, mainly the Velus package
  outputs =
    inputs@{
      self,
      flake-parts,
      nixpkgs,
    }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      # Supported architectures
      systems = [
        "aarch64-macos"
        "x86_64-linux"
      ];

      perSystem =
        { pkgs, system, ... }:
        let
          # Source of coq and OCaml packages for all the built packages.
          # Change the version of coq here and it should be propagated everywhere.
          coqPackages = pkgs.coqPackages_8_20;
          ocamlPackages = coqPackages.coq.ocamlPackages;
        in
        {
          packages = rec {
            # CompCert package, patched for velus
            #
            # You can check <https://github.com/NixOS/nixpkgs/blob/master/pkgs/development/coq-modules/compcert/default.nix>
            # to see the official package on nixpkgs.
            compCert = pkgs.stdenv.mkDerivation {
              name = "CompCert";
              # Change the rev and the hash when the CompCert submodule is updated
              src = pkgs.fetchFromGitHub {
                owner = "inria-parkas";
                repo = "CompCert";
                rev = "v3.16-velus";
                hash = "sha256-eBqkLPNgFPqeFUxOKchJ9gkwaMjAocx6/JcUAl1nYRw=";
              };

              nativeBuildInputs =
                with ocamlPackages;
                [
                  findlib
                  menhir
                  ocaml
                ]
                ++ (with coqPackages; [
                  coq
                ]);
              buildInputs = with ocamlPackages; [ menhirLib ];
              propagatedBuildInputs = with coqPackages; [
                flocq
                MenhirLib
              ];

              enableParallelBuilding = true;

              patchPhase = ''
                runHook prePatch

                patchShebangs configure

                runHook postPatch
              '';

              preConfigure = ''
                configureFlagsArray=(
                  -prefix $prefix
                  -clightgen
                  -use-external-Flocq
                  -use-external-MenhirLib
                  ${system}
                )
              '';
              dontAddPrefix = true;

              preBuild = ''
                for dir in $(find . -maxdepth 1 -type d ! -name ".*"); do
                  echo $dir/*.ml* $out/lib/compcert/coq/$dir/;
                done
              '';

              postInstall = ''
                install -m0644 Makefile.config Makefile.menhir $out/lib/compcert/coq/
                cp -R debug $out/lib/compcert/coq/debug
                find . -mindepth 2 -type f -name "*.*ml*" -exec install -m0644 {} $out/lib/compcert/coq/{} \;
              '';
            };

            # Velus package
            velus = pkgs.stdenv.mkDerivation {
              name = "velus";
              src = ./.;

              # Compile-time dependencies
              nativeBuildInputs =
                with pkgs;
                [
                  ncurses
                ]
                ++ (with ocamlPackages; [
                  findlib
                  menhir
                  menhirLib
                  ocaml
                  ocamlbuild
                  ocamlgraph
                ])
                ++ (with coqPackages; [
                  coq
                ]);

              # Runtime dependencies
              buildInputs = [
                compCert
              ];

              enableParallelBuilding = true;

              patchPhase = ''
                runHook prePatch

                patchShebangs configure
                sed -i 's;proof: compcert;proof:;' Makefile
                sed -i "s;\$(COMPCERTDIR)/compcert.ini;${compCert}/share/compcert.ini;" Makefile

                runHook postPatch
              '';

              preConfigure = ''
                configureFlagsArray=(
                  -prefix $prefix
                  -velus-only
                  -compcertdir ${compCert}/lib/compcert/coq
                  -flocqdir ${coqPackages.flocq}/lib/coq/${coqPackages.coq.coq-version}/user-contrib/Flocq
                  -menhirlibdir ${coqPackages.MenhirLib}/lib/coq/${coqPackages.coq.coq-version}/user-contrib/MenhirLib
                  ${system}
                )
              '';
              dontAddPrefix = true;

              installPhase = ''
                mkdir -p $out/bin
                install -m0755 ./velus $out/bin/velus
                install -m0644 ./_build/src/compcert.ini $out/bin/compcert.ini
              '';
            };

            default = velus;
          };
        };
    };
}
