# shell.nix
let
  pkgs = import <nixos-unstable> {};

  tex = (pkgs.texlive.combine {
    inherit (pkgs.texlive) scheme-basic amsmath mathtools
      latexmk xetex etoolbox unicode-math dvisvgm pdfcrop geometry;
  });
  python = pkgs.python3.override {
    self = python;
    packageOverrides = pyfinal: pyprev: {
      leanblueprint = pyfinal.callPackage ./leanblueprint.nix {};
    };
  };

in pkgs.mkShell {
  packages = [
    tex
    pkgs.graphviz
    pkgs.ghostscript
    pkgs.pdf2svg
    (python.withPackages (python-pkgs: with python-pkgs; [
      pygraphviz
      leanblueprint
    ]))
  ];
}
