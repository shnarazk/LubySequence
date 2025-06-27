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
            colorschemes.gruvbox.enable = true;
            dependencies.lean.enable = false;
            globals = {
              mapleader = " ";
              maplocalleader = "  ";
            };
            lsp.inlayHints.enable = true;
            lsp.keymaps = [
              {
                key = "gd";
                lspBufAction = "definition";
              }
              {
                key = "gD";
                lspBufAction = "references";
              }
              {
                key = "gt";
                lspBufAction = "type_definition";
              }
              {
                key = "gi";
                lspBufAction = "implementation";
              }
              {
                key = "k";
                lspBufAction = "hover";
              }
            ];
            plugins.blink-cmp = {
              enable = true;
              settings.keymap = {
                preset = "enter";
              };
              settings.sources = {
                default = [
                  "lsp"
                  "path"
                  "buffer"
                  "copilot"
                ];
                providers = {
                  copilot = {
                    async = true;
                    module = "blink-copilot";
                    name = "copilot";
                    score_offset = 100;
                    # Optional configurations
                    opts = {
                      max_completions = 3;
                      max_attempts = 4;
                      kind = "Copilot";
                      debounce = 750;
                      auto_refresh = {
                        backward = true;
                        forward = true;
                      };
                    };
                  };
                };
              };
            };
            plugins.blink-copilot.enable = true;
            plugins.lean.enable = true;
            plugins.lean.autoLoad = true;
            plugins.lean.settings.mappings = true;
            plugins.lean.settings.progress_bars.enable = false;
            plugins.lualine.enable = true;
            # plugins.lualine.settings.options.icons_enabled = false;
            plugins.nvim-surround.enable = true;
            plugins.which-key.enable = true;
            # plugins.which-key.settings.icons.keys = {
            #   BS = "BS";
            #   C = "C-";
            #   CR = "CR";
            #   D = "D-";
            #   Down = "↓";
            #   Esc = "Esc";
            #   F1 = "F1";
            #   F10 = "F10";
            #   F11 = "F11";
            #   F12 = "F12";
            #   F2 = "F2";
            #   F3 = "F3";
            #   F4 = "F4";
            #   F5 = "F5";
            #   F6 = "F6";
            #   F7 = "F7";
            #   F8 = "F8";
            #   F9 = "F9";
            #   Left = "←";
            #   M = "M-";
            #   NL = "NL";
            #   Right = "→";
            #   S = "S-";
            #   ScrollWheelDown = "⇣";
            #   ScrollWheelUp = "⇡";
            #   Space = "SPC";
            #   Tab = "TAB";
            #   Up = "↑";
            # };
            # plugins.which-key.settings.icons.rules = false;
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
