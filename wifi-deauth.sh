#!/bin/sh
echo Starting Massive-Wifi-Deauth
DISPLAY=:0 exec  xterm -e "cd /home/kali/Desktop/wifi-deauth/;sudo python3 wifi-deauth.py -i wlan0  -e exclude_bssid.txt -k -t 10 -n 100" &
exit 0
