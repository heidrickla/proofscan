
# proofscan self-check: a cloudhook made in a flow and deleted only by the flow's own removal.
from homeassistant.components import cloud


class PsFlow:
    async def async_step_user(self, user_input=None):
        self.url = await cloud.async_create_cloudhook(self.hass, "ps_hook")
        return self.async_show_form(step_id="user")

    async def async_remove(self):
        await cloud.async_delete_cloudhook(self.hass, "ps_hook")
