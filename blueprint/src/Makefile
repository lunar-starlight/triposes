.PHONY: plastex
plastex:
	nix-shell --run "sudo plastex -c plastex.cfg web.tex"
.PHONY: pdf
pdf:
	nix-shell --run "leanblueprint pdf"
.PHONY: all
all:
	nix-shell --run "leanblueprint pdf; sudo plastex -c plastex.cfg web.tex; leanblueprint checkdecls"
.PHONY: serve
serve:
	nix-shell --run "leanblueprint serve"
