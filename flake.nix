{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.systems.url = "github:nix-systems/default";
  inputs.flake-utils = {
    url = "github:numtide/flake-utils";
    inputs.systems.follows = "systems";
  };

  outputs =
    { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell { packages = [
          pkgs.bashInteractive
          pkgs.elan
          (pkgs.texlive.combine {
            inherit (pkgs.texlive)
              scheme-small lkproof fontawesome5 haranoaji ifoddpage
              latexmk luatexja noto tcolorbox tex4ht textpos
              tikz-ext tikzfill tikzpagenodes;
          })
          pkgs.vscodium
        ]; };
      }
    );
}
