class CountInvocations:
    """A class decorator that counts function invocations."""
    def __init__(self, func):
        self._func = func
        self._invocations = 0

    def __call__(self, *args, **kwargs):
        self._invocations += 1
        return self._func(*args, **kwargs)

    def clear(self):
        self._invocations = 0

    @property
    def invocations(self):
        return self._invocations
