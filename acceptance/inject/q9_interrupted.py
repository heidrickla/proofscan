
# proofscan self-check: a holder released in a finally block after a call that can raise.
class PsTyping:
    def __init__(self) -> None:
        self._typing_holder = None

    async def ps_type(self, keypad, send) -> None:
        self._typing_holder = keypad
        try:
            await send(keypad)
        finally:
            await send(None)
            self._typing_holder = None
