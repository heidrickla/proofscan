
# proofscan self-check: a token from the environment written to a log.
import logging
import os

_LOGGER = logging.getLogger(__name__)


def ps_connect() -> str:
    token = os.environ.get("PS_API_TOKEN", "")
    _LOGGER.info("connecting with %s", token)
    return token
