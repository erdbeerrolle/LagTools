.PHONY: test compare

# Fast unit tests (no model loading, no symbolic simplification)
test:
	@bash scripts/run_tests.sh Tests.wlt

# Full reference comparison: all vertices, propagators, and 2-point counterterms
# against the literature (slow — runs FullSimplify over ~100 rules)
compare:
	@bash scripts/run_tests.sh feynRulesCompare.wlt
