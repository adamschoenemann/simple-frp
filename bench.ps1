stack build --profile
if ($LastExitCode -eq 0) {
  .\.stack-work\dist\ca59d0ab\build\frp-profile\frp-profile.exe +RTS -hc "-i1"
  hp2ps -e8in -c .\frp-profile.hp
  ps2pdf .\frp-profile.ps
}
