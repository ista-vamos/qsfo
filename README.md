# qsfo

Quantitative Signal First-Order Logic

## Setup

Install `uv`, run:

```sh
uv sync
```

Then, run all commands through `uv run`, e.g.:

```
uv run main.py
```

Alternatively, you can enter a shell with the `uv` environment like this:

```
uv run $SHELL

# now you can run commands without "uv run"
./main.py
```

## Setup via pip

```sh
# setup python virtual environment
python3 -mvenv .venv/
source .venv/bin/activate

pip install lark sympy pplpy
```

Then, in every terminal from where you run the project,
you must first call

```sh
source .venv/bin/activate
```
