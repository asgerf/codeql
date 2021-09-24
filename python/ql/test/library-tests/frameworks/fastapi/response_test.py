# see https://fastapi.tiangolo.com/advanced/response-cookies/

from fastapi import FastAPI, Response
import asyncio

app = FastAPI()


@app.get("/response_parameter") # $ routeSetup="/response_parameter"
async def response_parameter(response: Response): # $ requestHandler
    response.set_cookie("key", "value") # $ CookieWrite CookieName="key" CookieValue="value"
    response.set_cookie(key="key", value="value") # $ CookieWrite CookieName="key" CookieValue="value"
    response.headers.append("Set-Cookie", "key2=value2") # $ CookieWrite CookieRawHeader="key2=value2"
    response.headers.append(key="Set-Cookie", value="key2=value2") # $ CookieWrite CookieRawHeader="key2=value2"
    response.headers["X-MyHeader"] = "header-value"
    response.status_code = 418
    return {"message": "response as parameter"} # $ HttpResponse mimetype=application/json responseBody=Dict


@app.get("/resp_parameter") # $ routeSetup="/resp_parameter"
async def resp_parameter(resp: Response): # $ requestHandler
    resp.status_code = 418
    return {"message": "resp as parameter"} # $ HttpResponse mimetype=application/json responseBody=Dict


@app.get("/response_parameter_no_type") # $ routeSetup="/response_parameter_no_type"
async def response_parameter_no_type(response): # $ requestHandler routedParameter=response
    # NOTE: This does in fact not work, since FastAPI relies on the type annotations,
    # and not on the name of the parameter
    response.status_code = 418
    return {"message": "response as parameter"} # $ HttpResponse mimetype=application/json responseBody=Dict


# Direct response construction

# see https://fastapi.tiangolo.com/advanced/response-directly/
# see https://fastapi.tiangolo.com/advanced/custom-response/

import fastapi.responses


@app.get("/direct_response") # $ routeSetup="/direct_response"
async def direct_response(): # $ requestHandler
    xml_data = "<foo>FOO</foo>"
    resp = fastapi.responses.Response(xml_data, 200, None, "application/xml") # $ MISSING: HttpResponse mimetype=application/xml responseBody=xml_data
    resp = fastapi.responses.Response(content=xml_data, media_type="application/xml") # $ MISSING: HttpResponse mimetype=application/xml responseBody=xml_data
    return resp # $ SPURIOUS: HttpResponse mimetype=application/json responseBody=resp


@app.get("/direct_response2", response_class=fastapi.responses.Response) # $ routeSetup="/direct_response2"
async def direct_response2(): # $ requestHandler
    xml_data = "<foo>FOO</foo>"
    return xml_data # $ HttpResponse responseBody=xml_data SPURIOUS: mimetype=application/json


class MyXmlResponse(fastapi.responses.Response):
    media_type = "application/xml"


@app.get("/my_xml_response") # $ routeSetup="/my_xml_response"
async def my_xml_response(): # $ requestHandler
    xml_data = "<foo>FOO</foo>"
    resp = MyXmlResponse(content=xml_data) # $ MISSING: HttpResponse mimetype=application/xml responseBody=xml_data
    return resp # $ SPURIOUS: HttpResponse mimetype=application/json responseBody=resp


@app.get("/my_xml_response2", response_class=MyXmlResponse) # $ routeSetup="/my_xml_response2"
async def my_xml_response2(): # $ requestHandler
    xml_data = "<foo>FOO</foo>"
    return xml_data # $ HttpResponse responseBody=xml_data SPURIOUS: mimetype=application/json MISSING: mimetype=application/xml


@app.get("/html_response") # $ routeSetup="/html_response"
async def html_response(): # $ requestHandler
    hello_world = "<h1>Hello World!</h1>"
    resp =  fastapi.responses.HTMLResponse(hello_world) # $ MISSING: HttpResponse mimetype=text/html responseBody=hello_world
    return resp # $ SPURIOUS: HttpResponse mimetype=application/json responseBody=resp


@app.get("/html_response2", response_class=fastapi.responses.HTMLResponse) # $ routeSetup="/html_response2"
async def html_response2(): # $ requestHandler
    hello_world = "<h1>Hello World!</h1>"
    return hello_world # $ HttpResponse responseBody=hello_world SPURIOUS: mimetype=application/json MISSING: mimetype=text/html


@app.get("/redirect") # $ routeSetup="/redirect"
async def redirect(): # $ requestHandler
    next = "https://www.example.com"
    resp = fastapi.responses.RedirectResponse(next) # $ MISSING: HttpResponse HttpRedirectResponse redirectLocation=next
    return resp # $ SPURIOUS: HttpResponse mimetype=application/json responseBody=resp


@app.get("/redirect2", response_class=fastapi.responses.RedirectResponse) # $ routeSetup="/redirect2"
async def redirect2(): # $ requestHandler
    next = "https://www.example.com"
    return next # $ HttpResponse SPURIOUS: mimetype=application/json responseBody=next MISSING: HttpRedirectResponse redirectLocation=next


@app.get("/streaming_response") # $ routeSetup="/streaming_response"
async def streaming_response(): # $ requestHandler
    # You can test this with curl:
    # curl --no-buffer http://127.0.0.1:8000/streaming_response
    async def content():
        yield b"Hello "
        await asyncio.sleep(0.5)
        yield b"World"
        await asyncio.sleep(0.5)
        yield b"!"

    resp = fastapi.responses.StreamingResponse(content()) # $ MISSING: HttpResponse responseBody=content()
    return resp # $ SPURIOUS: HttpResponse mimetype=application/json responseBody=resp


# setting `response_class` to `StreamingResponse` does not seem to work
# so no such example here


@app.get("/file_response") # $ routeSetup="/file_response"
async def file_response(): # $ requestHandler
    # has internal dependency on PyPI package `aiofiles`
    # will guess MIME type from file extension

    # We don't really have any good QL modeling of passing a file-path, whose content
    # will be returned as part of the response... so will leave this as a TODO for now.
    resp = fastapi.responses.FileResponse(__file__) # $ MISSING: HttpResponse
    return resp # $ SPURIOUS: HttpResponse mimetype=application/json responseBody=resp


@app.get("/file_response2", response_class=fastapi.responses.FileResponse) # $ routeSetup="/file_response2"
async def file_response2(): # $ requestHandler
    return __file__ # $ HttpResponse SPURIOUS: mimetype=application/json responseBody=__file__
