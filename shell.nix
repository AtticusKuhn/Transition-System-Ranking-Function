{ pkgs ? import <nixpkgs-unstable> {} }:
with pkgs;
mkShell {
  buildInputs = [
    pkgs.unzip
    pkgs.aider-chat
  ];
shellHook = ''
# lake exe cache get!
# lake build
# code
'';
}
