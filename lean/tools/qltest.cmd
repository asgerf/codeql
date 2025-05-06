@echo off

type NUL && "%CODEQL_DIST%\codeql.exe" database index-files ^
    --prune=**/*.testproj ^
    --include-extension=.js ^
    --size-limit=5m ^
    --language=lean ^
    --working-dir=. ^
    "%CODEQL_EXTRACTOR_LEAN_WIP_DATABASE%"

IF %ERRORLEVEL% NEQ 0 exit /b %ERRORLEVEL%

exit /b %ERRORLEVEL%
