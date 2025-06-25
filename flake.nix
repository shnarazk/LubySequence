{
  description = "A basic flake with a shell";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
  inputs.systems.url = "github:nix-systems/default";
  inputs.flake-utils = {
    url = "github:numtide/flake-utils";
    inputs.systems.follows = "systems";
  };
  inputs.nixvim.url = "github:nix-community/nixvim";

  outputs =
    { nixpkgs, flake-utils, nixvim, ... }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        nvim = nixvim.legacyPackages.${system};
      in
      {
        devShells.default = pkgs.mkShell { packages = [
          pkgs.bashInteractive
          pkgs.elan
          (nvim.makeNixvim {
            plugins.lean.enable = true;
            plugins.lean.autoLoad = true;
            # plugins.tree-sitter.enable = true;
            # plugins.treesitter-textobjects.enable = true;
          })
          pkgs.texlab
          (pkgs.texlive.combine {
            inherit (pkgs.texlive)
              scheme-small lkproof fontawesome5 haranoaji ifoddpage
              latexmk luatexja luaxml make4ht noto tcolorbox
              tex4ht textpos tikz-ext tikzfill tikzpagenodes;
          })
          # pkgs.vscodium
        ]; };
      }
    );
}
