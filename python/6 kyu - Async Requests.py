from preloaded import send_request
import asyncio


async def request_manager(n: int) -> str:
    res = await asyncio.gather(*(send_request() for _ in range(n)))
    return ''.join(res)
