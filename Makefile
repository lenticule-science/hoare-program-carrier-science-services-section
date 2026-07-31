SHELL := /usr/bin/bash
.DEFAULT_GOAL := help

.PHONY: help build check

help: ## Show every procedure
	@echo "Hoare-program carrier procedures — run 'make <target>':"
	@grep -hE '^[a-z][a-z-]*:.*##' $(MAKEFILE_LIST) | sort | awk -F':.*##[ ]*' '{printf "  %-10s %s\n", $$1, $$2}'

build: ## Build the Lean library and its Obsmetrologia dependency
	lake build

check: ## Build the library and print its axiom audit
	lake build
	lake env lean scripts/AxiomAudit.lean
