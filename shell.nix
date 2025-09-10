{ pkgs ? import <nixpkgs-unstable> {} }:
with pkgs;
mkShell {
  buildInputs = [
    pkgs.unzip
    pkgs.aider-chat
    pkgs.codex
    pkgs.uv
  ];
shellHook = ''
# lake exe cache get!
# lake build
# code
'';
}
