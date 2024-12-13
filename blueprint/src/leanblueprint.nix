# leanblueprint.nix
{
  lib,
  buildPythonPackage,
  fetchPypi,
  setuptools,
  wheel,

  plasTeX,
  plastexshowmore,
  plastexdepgraph,
  click,
  rich,
  rich-click,
  tomlkit,
  jinja2,
  gitpython,
}:

buildPythonPackage rec {
  pname = "leanblueprint";
  version = "0.0.16";

  src = fetchPypi {
    inherit pname version;
    hash = "sha256-DgoSgHox+hupztn8AaqFsIxekZq59mL3rx5N7SB5rPc=";
  };

  dependencies = [
    plasTeX
    plastexshowmore
    plastexdepgraph
    click
    rich
    rich-click
    tomlkit
    gitpython
  ];
  
  doCheck = false;

  pyproject = true;
  build-system = [
    setuptools
    wheel
  ];
}
