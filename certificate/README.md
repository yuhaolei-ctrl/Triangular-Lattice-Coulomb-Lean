# Reference computations

`manuscript_v2/` contains the interval-arithmetic scripts of the manuscript (version v2,
Appendices A–C), unchanged. They need Python 3.10+ and `python-flint >= 0.9`:

```sh
python3 -m venv venv && venv/bin/pip install python-flint
venv/bin/python manuscript_v2/verify_lemma21.py   # about two minutes
venv/bin/python manuscript_v2/constants.py
```

These scripts are not part of the Lean proof. The Lean certificate (layer 5 of
[`docs/PLAN.md`](../docs/PLAN.md)) is a redesigned computation checked by Lean's kernel; the scripts
that produce its data will be added here.
