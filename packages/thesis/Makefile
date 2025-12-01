MKDOCS_CONFIG := mkdocs.yml

.PHONY: docs-html docs-serve docs-lint

docs-html:
	mkdocs build -f $(MKDOCS_CONFIG)

docs-serve:
	mkdocs serve -f $(MKDOCS_CONFIG) --dev-addr 0.0.0.0:8000

docs-lint:
	scripts/lint_math.py
