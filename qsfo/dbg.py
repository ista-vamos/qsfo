import functools

_trace_indent: int = 0


def trace_calls(func):
    """
    Decorator to log function calls, including parameters, arguments, and return values.
    """

    @functools.wraps(func)
    def wrapper(*args, **kwargs):  # Print function call details before execution
        # return func(*args, **kwargs)

        global _trace_indent
        print(" " * _trace_indent, f"\033[0;33m-->: {func.__name__}:")
        for n, a in enumerate(args):
            print(" " * _trace_indent, f"  {n} -> {a}")
        for k, a in kwargs:
            print(" " * _trace_indent, f"  {n} -> {k}={a}")
        print("\033[0m", end="")

        try:
            # Execute the original function
            _trace_indent += 2
            result = func(*args, **kwargs)
            _trace_indent -= 2
            # Print return value after execution
            print(" " * _trace_indent, f"\033[0;32m<-- {func.__name__}:", end=" ")
            print(" " * _trace_indent, f"  {result}")
            print("\033[0m", end="")
            return result
        except Exception as e:
            # Print exception if one occurs
            print(
                f"\033[0;31mException in {func.__module__}.{func.__name__}: {e}\033[0m"
            )
            raise

    return wrapper


def add_to_indent(i):
    global _trace_indent
    _trace_indent += i


def add_to_trace(msg, *args):
    print(" " * _trace_indent, f"\033[0;36m{msg}")
    for a in args:
        print(" " * _trace_indent, f".. {a}")
    print("\033[0m", end="")
