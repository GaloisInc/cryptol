& "$env:WIX\bin\heat.exe" dir "$pwd/dist" -o allfiles.wxs -nologo -var var.pkg -ag -wixvar -cg ALLFILES -srd -dr INSTALLDIR -sfrag
& "$env:WIX\bin\candle.exe" -ext WixUIExtension -ext WixUtilExtension -dversion="$env:VERSION" win32\cryptol.wxs
& "$env:WIX\bin\candle.exe" -ext WixUIExtension -ext WixUtilExtension -dversion="$env:VERSION" -dpkg="$pwd/dist" allfiles.wxs
& "$env:WIX\bin\light.exe" -ext WixUIExtension -ext WixUtilExtension -sval -o cryptol.msi cryptol.wixobj allfiles.wixobj
