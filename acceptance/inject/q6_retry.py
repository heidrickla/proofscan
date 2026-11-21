
# proofscan self-check: a retry loop with no limit.
def ps_fetch(get):
    while True:
        try:
            return get()
        except OSError:
            pass
