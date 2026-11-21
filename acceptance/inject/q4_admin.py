
# proofscan self-check: a service action that writes a registry, registered without an admin check.
from homeassistant.core import HomeAssistant, ServiceCall
from homeassistant.helpers import device_registry as dr


async def ps_setup_services(hass: HomeAssistant) -> None:
    async def _ps_rename(call: ServiceCall) -> None:
        reg = dr.async_get(hass)
        reg.async_update_device(call.data["device_id"], name_by_user=call.data["name"])

    hass.services.async_register("power_fingerprint", "ps_rename", _ps_rename)
