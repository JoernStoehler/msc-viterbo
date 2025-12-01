from viterbo.experiments.hello.stage_hello import run


def test_run_returns_greeting_and_sum():
    result = run("tester", [1, 2, 3])
    assert result["greeting"].startswith("Hello, Tester")
    assert result["alternating_sum"] == 1 - 2 + 3
