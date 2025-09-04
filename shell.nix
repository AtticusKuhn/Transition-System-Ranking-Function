{ pkgs ? import <nixpkgs-unstable> {} }:
with pkgs;
mkShell {
  buildInputs = [
    pkgs.unzip
    pkgs.aider-chat
    pkgs.codex
  ];
shellHook = ''
# lake exe cache get!
# lake build
# code
'';
}
