{ nixpkgs ? <nixpkgs> }:
let
  pkgs = import (builtins.fetchTarball {
    name = "nixos-unstable-2018-12-08";
    url = https://github.com/nixos/nixpkgs/archive/e85c1f586807b5acd244df4c45a5130aa3f0734d.tar.gz;
    sha256 = "1xy1qgam0i2fyqhaczw0qrx8yv3hgdh9jp47wmln5ljiixr5ic5n";
    }) {};
  stdenv = pkgs.stdenv;
  eggs = import ./eggs.nix { inherit pkgs stdenv; };
  idrisWithPkgs = pkgs.idrisPackages.with-packages (with pkgs.idrisPackages; [ contrib pruviloj ]);
in
with pkgs; stdenv.mkDerivation {
  name = "blodwen-shell-extras";
  buildInputs = [
    gmp chez idrisWithPkgs chicken eggs.numbers bazel
  ];
}
