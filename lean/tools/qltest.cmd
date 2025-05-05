@echo off

type NUL && "%CODEQL_DIST%\codeql.exe" database index-files ^
    --prune=**/*.testproj ^
    --include-extension=.php ^
    --size-limit=5m ^
    --language=lean ^
    --working-dir=. ^
    "%CODEQL_EXTRACTOR_QL_WIP_DATABASE%"

IF %ERRORLEVEL% NEQ 0 exit /b %ERRORLEVEL%

exit /b %ERRORLEVEL%
