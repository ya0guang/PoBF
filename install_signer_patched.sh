#!/bin/sh
# This script was generated using Makeself 2.4.5
# The license covering this archive and its contents, if any, is wholly independent of the Makeself license (GPL)

ORIG_UMASK=`umask`
if test "n" = n; then
    umask 077
fi

CRCsum="3622332557"
MD5="1a3393fb43b15c291b9d4e3802fe1b8e"
SHA="0000000000000000000000000000000000000000000000000000000000000000"
SIGNATURE=""
TMPROOT=${TMPDIR:=/tmp}
USER_PWD="$PWD"
export USER_PWD
ARCHIVE_DIR=`dirname "$0"`
export ARCHIVE_DIR

label="SGX Signer Installation"
script="./install.sh"
scriptargs=""
cleanup_script=""
licensetxt=""
helpheader=''
targetdir="sign_sign"
filesizes="91353"
totalsize="91353"
keep="n"
nooverwrite="n"
quiet="n"
accept="n"
nodiskspace="n"
export_conf="n"
decrypt_cmd=""
skip="713"

print_cmd_arg=""
if type printf > /dev/null; then
    print_cmd="printf"
elif test -x /usr/ucb/echo; then
    print_cmd="/usr/ucb/echo"
else
    print_cmd="echo"
fi

if test -d /usr/xpg4/bin; then
    PATH=/usr/xpg4/bin:$PATH
    export PATH
fi

if test -d /usr/sfw/bin; then
    PATH=$PATH:/usr/sfw/bin
    export PATH
fi

unset CDPATH

MS_Printf()
{
    $print_cmd $print_cmd_arg "$1"
}

MS_PrintLicense()
{
  PAGER=${PAGER:=more}
  if test x"$licensetxt" != x; then
    PAGER_PATH=`exec <&- 2>&-; which $PAGER || command -v $PAGER || type $PAGER`
    if test -x "$PAGER_PATH"; then
      echo "$licensetxt" | $PAGER
    else
      echo "$licensetxt"
    fi
    if test x"$accept" != xy; then
      while true
      do
        MS_Printf "Please type y to accept, n otherwise: "
        read yn
        if test x"$yn" = xn; then
          keep=n
          eval $finish; exit 1
          break;
        elif test x"$yn" = xy; then
          break;
        fi
      done
    fi
  fi
}

MS_diskspace()
{
	(
	df -kP "$1" | tail -1 | awk '{ if ($4 ~ /%/) {print $3} else {print $4} }'
	)
}

MS_dd()
{
    blocks=`expr $3 / 1024`
    bytes=`expr $3 % 1024`
    # Test for ibs, obs and conv feature
    if dd if=/dev/zero of=/dev/null count=1 ibs=512 obs=512 conv=sync 2> /dev/null; then
        dd if="$1" ibs=$2 skip=1 obs=1024 conv=sync 2> /dev/null | \
        { test $blocks -gt 0 && dd ibs=1024 obs=1024 count=$blocks ; \
          test $bytes  -gt 0 && dd ibs=1 obs=1024 count=$bytes ; } 2> /dev/null
    else
        dd if="$1" bs=$2 skip=1 2> /dev/null
    fi
}

MS_dd_Progress()
{
    if test x"$noprogress" = xy; then
        MS_dd "$@"
        return $?
    fi
    file="$1"
    offset=$2
    length=$3
    pos=0
    bsize=4194304
    while test $bsize -gt $length; do
        bsize=`expr $bsize / 4`
    done
    blocks=`expr $length / $bsize`
    bytes=`expr $length % $bsize`
    (
        dd ibs=$offset skip=1 count=0 2>/dev/null
        pos=`expr $pos \+ $bsize`
        MS_Printf "     0%% " 1>&2
        if test $blocks -gt 0; then
            while test $pos -le $length; do
                dd bs=$bsize count=1 2>/dev/null
                pcent=`expr $length / 100`
                pcent=`expr $pos / $pcent`
                if test $pcent -lt 100; then
                    MS_Printf "\b\b\b\b\b\b\b" 1>&2
                    if test $pcent -lt 10; then
                        MS_Printf "    $pcent%% " 1>&2
                    else
                        MS_Printf "   $pcent%% " 1>&2
                    fi
                fi
                pos=`expr $pos \+ $bsize`
            done
        fi
        if test $bytes -gt 0; then
            dd bs=$bytes count=1 2>/dev/null
        fi
        MS_Printf "\b\b\b\b\b\b\b" 1>&2
        MS_Printf " 100%%  " 1>&2
    ) < "$file"
}

MS_Help()
{
    cat << EOH >&2
${helpheader}Makeself version 2.4.5
 1) Getting help or info about $0 :
  $0 --help   Print this message
  $0 --info   Print embedded info : title, default target directory, embedded script ...
  $0 --lsm    Print embedded lsm entry (or no LSM)
  $0 --list   Print the list of files in the archive
  $0 --check  Checks integrity of the archive
  $0 --verify-sig key Verify signature agains a provided key id

 2) Running $0 :
  $0 [options] [--] [additional arguments to embedded script]
  with following options (in that order)
  --confirm             Ask before running embedded script
  --quiet               Do not print anything except error messages
  --accept              Accept the license
  --noexec              Do not run embedded script (implies --noexec-cleanup)
  --noexec-cleanup      Do not run embedded cleanup script
  --keep                Do not erase target directory after running
                        the embedded script
  --noprogress          Do not show the progress during the decompression
  --nox11               Do not spawn an xterm
  --nochown             Do not give the target folder to the current user
  --chown               Give the target folder to the current user recursively
  --nodiskspace         Do not check for available disk space
  --target dir          Extract directly to a target directory (absolute or relative)
                        This directory may undergo recursive chown (see --nochown).
  --tar arg1 [arg2 ...] Access the contents of the archive through the tar command
  --ssl-pass-src src    Use the given src as the source of password to decrypt the data
                        using OpenSSL. See "PASS PHRASE ARGUMENTS" in man openssl.
                        Default is to prompt the user to enter decryption password
                        on the current terminal.
  --cleanup-args args   Arguments to the cleanup script. Wrap in quotes to provide
                        multiple arguments.
  --                    Following arguments will be passed to the embedded script
EOH
}

MS_Verify_Sig()
{
    GPG_PATH=`exec <&- 2>&-; which gpg || command -v gpg || type gpg`
    MKTEMP_PATH=`exec <&- 2>&-; which mktemp || command -v mktemp || type mktemp`
    test -x "$GPG_PATH" || GPG_PATH=`exec <&- 2>&-; which gpg || command -v gpg || type gpg`
    test -x "$MKTEMP_PATH" || MKTEMP_PATH=`exec <&- 2>&-; which mktemp || command -v mktemp || type mktemp`
	offset=`head -n "$skip" "$1" | wc -c | tr -d " "`
    temp_sig=`mktemp -t XXXXX`
    echo $SIGNATURE | base64 --decode > "$temp_sig"
    gpg_output=`MS_dd "$1" $offset $totalsize | LC_ALL=C "$GPG_PATH" --verify "$temp_sig" - 2>&1`
    gpg_res=$?
    rm -f "$temp_sig"
    if test $gpg_res -eq 0 && test `echo $gpg_output | grep -c Good` -eq 1; then
        if test `echo $gpg_output | grep -c $sig_key` -eq 1; then
            test x"$quiet" = xn && echo "GPG signature is good" >&2
        else
            echo "GPG Signature key does not match" >&2
            exit 2
        fi
    else
        test x"$quiet" = xn && echo "GPG signature failed to verify" >&2
        exit 2
    fi
}

MS_Check()
{
    OLD_PATH="$PATH"
    PATH=${GUESS_MD5_PATH:-"$OLD_PATH:/bin:/usr/bin:/sbin:/usr/local/ssl/bin:/usr/local/bin:/opt/openssl/bin"}
	MD5_ARG=""
    MD5_PATH=`exec <&- 2>&-; which md5sum || command -v md5sum || type md5sum`
    test -x "$MD5_PATH" || MD5_PATH=`exec <&- 2>&-; which md5 || command -v md5 || type md5`
    test -x "$MD5_PATH" || MD5_PATH=`exec <&- 2>&-; which digest || command -v digest || type digest`
    PATH="$OLD_PATH"

    SHA_PATH=`exec <&- 2>&-; which shasum || command -v shasum || type shasum`
    test -x "$SHA_PATH" || SHA_PATH=`exec <&- 2>&-; which sha256sum || command -v sha256sum || type sha256sum`

    if test x"$quiet" = xn; then
		MS_Printf "Verifying archive integrity..."
    fi
    offset=`head -n "$skip" "$1" | wc -c | tr -d " "`
    fsize=`cat "$1" | wc -c | tr -d " "`
    if test $totalsize -ne `expr $fsize - $offset`; then
        echo " Unexpected archive size." >&2
        exit 2
    fi
    verb=$2
    i=1
    for s in $filesizes
    do
		crc=`echo $CRCsum | cut -d" " -f$i`
		if test -x "$SHA_PATH"; then
			if test x"`basename $SHA_PATH`" = xshasum; then
				SHA_ARG="-a 256"
			fi
			sha=`echo $SHA | cut -d" " -f$i`
			if test x"$sha" = x0000000000000000000000000000000000000000000000000000000000000000; then
				test x"$verb" = xy && echo " $1 does not contain an embedded SHA256 checksum." >&2
			else
				shasum=`MS_dd_Progress "$1" $offset $s | eval "$SHA_PATH $SHA_ARG" | cut -b-64`;
				if test x"$shasum" != x"$sha"; then
					echo "Error in SHA256 checksums: $shasum is different from $sha" >&2
					exit 2
				elif test x"$quiet" = xn; then
					MS_Printf " SHA256 checksums are OK." >&2
				fi
				crc="0000000000";
			fi
		fi
		if test -x "$MD5_PATH"; then
			if test x"`basename $MD5_PATH`" = xdigest; then
				MD5_ARG="-a md5"
			fi
			md5=`echo $MD5 | cut -d" " -f$i`
			if test x"$md5" = x00000000000000000000000000000000; then
				test x"$verb" = xy && echo " $1 does not contain an embedded MD5 checksum." >&2
			else
				md5sum=`MS_dd_Progress "$1" $offset $s | eval "$MD5_PATH $MD5_ARG" | cut -b-32`;
				if test x"$md5sum" != x"$md5"; then
					echo "Error in MD5 checksums: $md5sum is different from $md5" >&2
					exit 2
				elif test x"$quiet" = xn; then
					MS_Printf " MD5 checksums are OK." >&2
				fi
				crc="0000000000"; verb=n
			fi
		fi
		if test x"$crc" = x0000000000; then
			test x"$verb" = xy && echo " $1 does not contain a CRC checksum." >&2
		else
			sum1=`MS_dd_Progress "$1" $offset $s | CMD_ENV=xpg4 cksum | awk '{print $1}'`
			if test x"$sum1" != x"$crc"; then
				echo "Error in checksums: $sum1 is different from $crc" >&2
				exit 2
			elif test x"$quiet" = xn; then
				MS_Printf " CRC checksums are OK." >&2
			fi
		fi
		i=`expr $i + 1`
		offset=`expr $offset + $s`
    done
    if test x"$quiet" = xn; then
		echo " All good."
    fi
}

MS_Decompress()
{
    if test x"$decrypt_cmd" != x""; then
        { eval "$decrypt_cmd" || echo " ... Decryption failed." >&2; } | eval "gzip -cd"
    else
        eval "gzip -cd"
    fi
    
    if test $? -ne 0; then
        echo " ... Decompression failed." >&2
    fi
}

UnTAR()
{
    if test x"$quiet" = xn; then
		tar $1vf -  2>&1 || { echo " ... Extraction failed." >&2; kill -15 $$; }
    else
		tar $1f -  2>&1 || { echo Extraction failed. >&2; kill -15 $$; }
    fi
}

MS_exec_cleanup() {
    if test x"$cleanup" = xy && test x"$cleanup_script" != x""; then
        cleanup=n
        cd "$tmpdir"
        eval "\"$cleanup_script\" $scriptargs $cleanupargs"
    fi
}

MS_cleanup()
{
    echo 'Signal caught, cleaning up' >&2
    MS_exec_cleanup
    cd "$TMPROOT"
    rm -rf "$tmpdir"
    eval $finish; exit 15
}

finish=true
xterm_loop=
noprogress=n
nox11=n
copy=none
ownership=n
verbose=n
cleanup=y
cleanupargs=
sig_key=

initargs="$@"

while true
do
    case "$1" in
    -h | --help)
	MS_Help
	exit 0
	;;
    -q | --quiet)
	quiet=y
	noprogress=y
	shift
	;;
	--accept)
	accept=y
	shift
	;;
    --info)
	echo Identification: "$label"
	echo Target directory: "$targetdir"
	echo Uncompressed size: 260 KB
	echo Compression: gzip
	if test x"n" != x""; then
	    echo Encryption: n
	fi
	echo Date of packaging: Thu Aug  4 22:58:01 EDT 2022
	echo Built with Makeself version 2.4.5
	echo Build command was: "/usr/bin/makeself \\
    \"./sign_sign\" \\
    \"./install.sh\" \\
    \"SGX Signer Installation\" \\
    \"./install.sh\""
	if test x"$script" != x; then
	    echo Script run after extraction:
	    echo "    " $script $scriptargs
	fi
	if test x"" = xcopy; then
		echo "Archive will copy itself to a temporary location"
	fi
	if test x"n" = xy; then
		echo "Root permissions required for extraction"
	fi
	if test x"n" = xy; then
	    echo "directory $targetdir is permanent"
	else
	    echo "$targetdir will be removed after extraction"
	fi
	exit 0
	;;
    --dumpconf)
	echo LABEL=\"$label\"
	echo SCRIPT=\"$script\"
	echo SCRIPTARGS=\"$scriptargs\"
    echo CLEANUPSCRIPT=\"$cleanup_script\"
	echo archdirname=\"sign_sign\"
	echo KEEP=n
	echo NOOVERWRITE=n
	echo COMPRESS=gzip
	echo filesizes=\"$filesizes\"
    echo totalsize=\"$totalsize\"
	echo CRCsum=\"$CRCsum\"
	echo MD5sum=\"$MD5sum\"
	echo SHAsum=\"$SHAsum\"
	echo SKIP=\"$skip\"
	exit 0
	;;
    --lsm)
cat << EOLSM
No LSM.
EOLSM
	exit 0
	;;
    --list)
	echo Target directory: $targetdir
	offset=`head -n "$skip" "$0" | wc -c | tr -d " "`
	for s in $filesizes
	do
	    MS_dd "$0" $offset $s | MS_Decompress | UnTAR t
	    offset=`expr $offset + $s`
	done
	exit 0
	;;
	--tar)
	offset=`head -n "$skip" "$0" | wc -c | tr -d " "`
	arg1="$2"
    shift 2 || { MS_Help; exit 1; }
	for s in $filesizes
	do
	    MS_dd "$0" $offset $s | MS_Decompress | tar "$arg1" - "$@"
	    offset=`expr $offset + $s`
	done
	exit 0
	;;
    --check)
	MS_Check "$0" y
	exit 0
	;;
    --verify-sig)
    sig_key="$2"
    shift 2 || { MS_Help; exit 1; }
    MS_Verify_Sig "$0"
    ;;
    --confirm)
	verbose=y
	shift
	;;
	--noexec)
	script=""
    cleanup_script=""
	shift
	;;
    --noexec-cleanup)
    cleanup_script=""
    shift
    ;;
    --keep)
	keep=y
	shift
	;;
    --target)
	keep=y
	targetdir="${2:-.}"
    shift 2 || { MS_Help; exit 1; }
	;;
    --noprogress)
	noprogress=y
	shift
	;;
    --nox11)
	nox11=y
	shift
	;;
    --nochown)
	ownership=n
	shift
	;;
    --chown)
        ownership=y
        shift
        ;;
    --nodiskspace)
	nodiskspace=y
	shift
	;;
    --xwin)
	if test "n" = n; then
		finish="echo Press Return to close this window...; read junk"
	fi
	xterm_loop=1
	shift
	;;
    --phase2)
	copy=phase2
	shift
	;;
	--ssl-pass-src)
	if test x"n" != x"openssl"; then
	    echo "Invalid option --ssl-pass-src: $0 was not encrypted with OpenSSL!" >&2
	    exit 1
	fi
	decrypt_cmd="$decrypt_cmd -pass $2"
    shift 2 || { MS_Help; exit 1; }
	;;
    --cleanup-args)
    cleanupargs="$2"
    shift 2 || { MS_Help; exit 1; }
    ;;
    --)
	shift
	break ;;
    -*)
	echo Unrecognized flag : "$1" >&2
	MS_Help
	exit 1
	;;
    *)
	break ;;
    esac
done

if test x"$quiet" = xy -a x"$verbose" = xy; then
	echo Cannot be verbose and quiet at the same time. >&2
	exit 1
fi

if test x"n" = xy -a `id -u` -ne 0; then
	echo "Administrative privileges required for this archive (use su or sudo)" >&2
	exit 1	
fi

if test x"$copy" \!= xphase2; then
    MS_PrintLicense
fi

case "$copy" in
copy)
    tmpdir="$TMPROOT"/makeself.$RANDOM.`date +"%y%m%d%H%M%S"`.$$
    mkdir "$tmpdir" || {
	echo "Could not create temporary directory $tmpdir" >&2
	exit 1
    }
    SCRIPT_COPY="$tmpdir/makeself"
    echo "Copying to a temporary location..." >&2
    cp "$0" "$SCRIPT_COPY"
    chmod +x "$SCRIPT_COPY"
    cd "$TMPROOT"
    exec "$SCRIPT_COPY" --phase2 -- $initargs
    ;;
phase2)
    finish="$finish ; rm -rf `dirname $0`"
    ;;
esac

if test x"$nox11" = xn; then
    if tty -s; then                 # Do we have a terminal?
	:
    else
        if test x"$DISPLAY" != x -a x"$xterm_loop" = x; then  # No, but do we have X?
            if xset q > /dev/null 2>&1; then # Check for valid DISPLAY variable
                GUESS_XTERMS="xterm gnome-terminal rxvt dtterm eterm Eterm xfce4-terminal lxterminal kvt konsole aterm terminology"
                for a in $GUESS_XTERMS; do
                    if type $a >/dev/null 2>&1; then
                        XTERM=$a
                        break
                    fi
                done
                chmod a+x $0 || echo Please add execution rights on $0
                if test `echo "$0" | cut -c1` = "/"; then # Spawn a terminal!
                    exec $XTERM -e "$0 --xwin $initargs"
                else
                    exec $XTERM -e "./$0 --xwin $initargs"
                fi
            fi
        fi
    fi
fi

if test x"$targetdir" = x.; then
    tmpdir="."
else
    if test x"$keep" = xy; then
	if test x"$nooverwrite" = xy && test -d "$targetdir"; then
            echo "Target directory $targetdir already exists, aborting." >&2
            exit 1
	fi
	if test x"$quiet" = xn; then
	    echo "Creating directory $targetdir" >&2
	fi
	tmpdir="$targetdir"
	dashp="-p"
    else
	tmpdir="$TMPROOT/selfgz$$$RANDOM"
	dashp=""
    fi
    mkdir $dashp "$tmpdir" || {
	echo 'Cannot create target directory' $tmpdir >&2
	echo 'You should try option --target dir' >&2
	eval $finish
	exit 1
    }
fi

location="`pwd`"
if test x"$SETUP_NOCHECK" != x1; then
    MS_Check "$0"
fi
offset=`head -n "$skip" "$0" | wc -c | tr -d " "`

if test x"$verbose" = xy; then
	MS_Printf "About to extract 260 KB in $tmpdir ... Proceed ? [Y/n] "
	read yn
	if test x"$yn" = xn; then
		eval $finish; exit 1
	fi
fi

if test x"$quiet" = xn; then
    # Decrypting with openssl will ask for password,
    # the prompt needs to start on new line
	if test x"n" = x"openssl"; then
	    echo "Decrypting and uncompressing $label..."
	else
        MS_Printf "Uncompressing $label"
	fi
fi
res=3
if test x"$keep" = xn; then
    trap MS_cleanup 1 2 3 15
fi

if test x"$nodiskspace" = xn; then
    leftspace=`MS_diskspace "$tmpdir"`
    if test -n "$leftspace"; then
        if test "$leftspace" -lt 260; then
            echo
            echo "Not enough space left in "`dirname $tmpdir`" ($leftspace KB) to decompress $0 (260 KB)" >&2
            echo "Use --nodiskspace option to skip this check and proceed anyway" >&2
            if test x"$keep" = xn; then
                echo "Consider setting TMPDIR to a directory with more free space."
            fi
            eval $finish; exit 1
        fi
    fi
fi

for s in $filesizes
do
    if MS_dd_Progress "$0" $offset $s | MS_Decompress | ( cd "$tmpdir"; umask $ORIG_UMASK ; UnTAR xp ) 1>/dev/null; then
		if test x"$ownership" = xy; then
			(cd "$tmpdir"; chown -R `id -u` .;  chgrp -R `id -g` .)
		fi
    else
		echo >&2
		echo "Unable to decompress $0" >&2
		eval $finish; exit 1
    fi
    offset=`expr $offset + $s`
done
if test x"$quiet" = xn; then
	echo
fi

cd "$tmpdir"
res=0
if test x"$script" != x; then
    if test x"$export_conf" = x"y"; then
        MS_BUNDLE="$0"
        MS_LABEL="$label"
        MS_SCRIPT="$script"
        MS_SCRIPTARGS="$scriptargs"
        MS_ARCHDIRNAME="$archdirname"
        MS_KEEP="$KEEP"
        MS_NOOVERWRITE="$NOOVERWRITE"
        MS_COMPRESS="$COMPRESS"
        MS_CLEANUP="$cleanup"
        export MS_BUNDLE MS_LABEL MS_SCRIPT MS_SCRIPTARGS
        export MS_ARCHDIRNAME MS_KEEP MS_NOOVERWRITE MS_COMPRESS
    fi

    if test x"$verbose" = x"y"; then
		MS_Printf "OK to execute: $script $scriptargs $* ? [Y/n] "
		read yn
		if test x"$yn" = x -o x"$yn" = xy -o x"$yn" = xY; then
			eval "\"$script\" $scriptargs \"\$@\""; res=$?;
		fi
    else
		eval "\"$script\" $scriptargs \"\$@\""; res=$?
    fi
    if test "$res" -ne 0; then
		test x"$verbose" = xy && echo "The program '$script' returned an error code ($res)" >&2
    fi
fi

MS_exec_cleanup

if test x"$keep" = xn; then
    cd "$TMPROOT"
    rm -rf "$tmpdir"
fi
eval $finish; exit $res
� 9��b�
�3h?X��Ԣi�ak�-��m�4,�u]5��T/Y5$Cv�{�Q�g�&v�P
�����{ι?��T�q-�3��Tg.)��^~������@�_�+��=]��wO_��IO�$����+�F�e�\���w�{�zL����up��	-s|"�K65��D4�2������q�0Yr�j�xn���_�}=N45i	�A�P���)�XF���C'd3�f��,k��|�����@ �f��r.��SΪ�䵬��syC��sjVf
�[��%��e�^�3T�����A�
wW<��7X��lt���ۃ׻��i�k<����s���Sz塞f��
�>E���)*�K��_��^�:޻l�J��}���n�C���`�I>@�]�q�����#�>
x	��Z��bs�71>��
�#��x�5�M���B|�G�ʛvN .��#�|/����'/"~��ĝ�sq�	�
��눏�UC���00^1$�Ʊ29�x?0^)$g�ƫ�dq0^!$��7��Ar�F`�2H��ƫ�d��U`�"Hz�_ƫ�d�E�ȟx� �'^
|5�/ �����$�9��ȟx:��O<	�:�'�8���' _O����?�X�/�?�(�ȟx��'|#�_
�ȟx)�$�'^ <����?H��s���?�t��ȟx���O|�T�'� <����O'����?�(��O<x&��E��W?J�8���ɟ8�1�'�<����?N�ħ�� ���O�?�a�r�'>����K��;��&��y�O���'��]�'^�,��
����<��8���ɟx��ȟx�����ie�Z�ܐ;�zo��;��Ԙ�sF~�a
��oAS�ox��)m����VO���=��c�tjy;p�TY��f�* �NuY	z���M���НUu�Q�*E�xctǨ�D���h�]��Z7�m�r�si?y�u�)W���d�����~���-�1/�1O��& <
�����Nmb��[}�D��l�2����}o�Ŵڀ6��(i���/61@���8��;�#�g����T=/@�A�$���A
�fo �+_��d,��f�G��c�^،�n�m��;/u�1ZW��78�P���
�:��r��^�/�V�9�Վ��J��8�uv�"|��;.U7�
�݁^*����ѩ^*�Z�rt�ڌ��ZFL�bs�ոO[jY/P���[�	�p�c,^�+;:��U�i�TG7;��s��m��]�+�vtU��5Z���%j��i]��k����#<�+T��=#4�)mœ��|	'�G$�Y*���-ilEbSk�Fh4[���W�Bݺ��tF A빎���3�caa��b]�pte	�3�j�lG77����|�[��%�^�r�kz�	G�^��zm����st��kI8=��S~c�&��z��|-l���-�A�L�b��u�����	�{�OX�i:k�7���F�;�_yP6Ba�W�հ�Qh1U�����xsm�v�J�}��÷N���ͺ}R�\��@�XS��HO�d� �^
��!_���w��\��%��XG�&#>�V��
{�ʦȕ�����,,u:�Z8��c
iA�Q��)G�B�T�,z����H������,�������ss���*��	���tzy�eyX>�(G���#Q�W��H/����" ù���6�>���T�z"կ���/d�����:)����|��,����3�B�Rb|���������wrNZ�'g������Hd�
����V���ip��cc�z��x���T���j�-�3��� ~�k˷AL���6�շ^p��w4��Eǁ�ߩ���Ջ0q��&�gz�q��lv{�&��<���RzA���A�.��_��$ғ�9�1�%��ao��gDx7��܇�s2�[ �2h���/5�}�]�c�dLjf��eK����ƌT]�O�]lC�x2YF�c�l ����b��g��V��tX]�+��N����ʻr<�&�;#�5�����u�h�%�zރӇe]���#/�9�GO��������Z1�
�������S�Nbs����h�l�
�xX 9�|
�ݭ7��}���#���ǖJ��aDw��%-"�8Z]�ҿ�P�L�*�ޙ�<�
�e_�7�!�3	�ґ{οmŦn���ѓS����e��sӄ�}�(����H�ۂ�REB��lY�w�)����,}�q�
���PQSE��t_6��r���b�]�s�1�m�?�*����P|A��u�A����Ϡ���~�Q؊�Z�����v��š���%"����{�?`0�����@��@^t*��^��<}<�S����qAl$l��F�������?��%k���XVg�9�����:@����.1��m��?������@4(��`�j䢭��S�S�dc4�`2_��C}�����$+�2l^}����Mr��hż�~��;}�ǳ(�(�F�e���{�9���g�,�r��'��R��Gw��L���D�s�g~�E�����5橗?�^�U=���?^�±�(�m���2^|IV�쩋?�M#���_Hv�ٍ|����{<�g��9U_Y�����<�5\�r�]qT�N��
�BǾ�Np/V��/I���w�ƈ7�2�-�
�$����馮O�Ҝ�"�m�)ɼ�l�U7i'"��W�~&P擴��*����:��,�snVo�zT���I��g�C�"o\��^s�>#���Nǉ�u�̣#�Kt�#���b�:�Qge����ՐT���N�8�$��j4���wkj���֭F�+/Ң�
�N�i������6��"F�!�6t��5�5����I��k��g+r���/����D?/������25�
M>)��֮=��j�3*HP���n�����z�(�`G�g^ʹ[��=��z�݈�4�ׯԼ����43-�T4�s E�*�h�{N���&ܽ��sfρS|�������5���Z�9{o)��ب�-B�Kԝ�N�F�=q�m�;u�9�_o�p��]���9��g�]�����y��P�&�^��:�_���{�
��`q�N`N�Y���������C���v5N�ߟ�0����)�x��+a�T7��+qU$�t��Y�	P����}g�=�H3�Z�8:�o!�ހ�"��e�:qrA��Փ�]p����_�<�~�Eۛ�}�i�2�^vR�s����b�W �'7�a�;D;�H)	СQ���:���u,c�ߍ��:�H��+��!�8��G�ܗ{�DGX�9��@!��#��5�s���G�+��}96IMȦr��ތ�*]��1�
�:�zs���Y�X��Og}������z
��H#�Xb�1�C8�1��k���(�{f�\��z�tփ�;Ǎ��U����X���⣈-��R6��#��(�0Px��G�[C5�O��Y�rYǺ��X�����)����\I9������V�Jd0h�=�������i�)G�k�i?����&��X vFч�a؍��}�8�^�i?��f�N��iW5�^~\�s�� ��ة2Ğ��gؘ�Fڑ�w�#mk���>.�ëͶ��Z��7��?������e�¸�L@��4b��Q��0��%����"As�D������$/q��4|7TW��ך�@o0E�1�*f̲r?~S���RL��	�$e?ځ~V���	K��p2��;�����c<���NRT��Jt��e�~��&�X9�������?���' �K%h�Lb`�l_��I/dIgb��#��O�r��T̬���\�}����?h^=��j����9���̟�ug�t�TX�V� ���+F����r��̴�(9,%%���JM}�Jb���z��d#�K�����|-`a��d"��"���
�*�Xt���!��i��RI	
���� }0X��N� %��V�Y�?lt��#�����.�Xb�!����
�=��Ք�W=�����]_����|݉���!����Z�K���L10H3E` o��h��CFS<[���҉Y�
��UJb��Hd���B�Q�\�_�?ܮ-�~7�c4[\-0����\ܯ~#���j�]^X��&�����9�w���\v�Hc!!�3��-upQ[*&��\�]�\���Ӷ��<d,?���/?�[��u�X~B��g����z,?�<ǯ.�m+5ݍ]OõR��Vj�]�W�X�(P��Qo7fD���7Fby����R&`��Cl'���غ����)ewng��Fݔ��>L\�Oh��/Q�7���3��#�׀y�ݖ�����uf�O�w���| ^��;z$>�E<��N\�A���F��9B������'ȈGrrs��<� ��|��1_ϙ�a��Ǎ��<��@���<�7^���ON.-���:�<���yB�G���Ԙ��ܒ��͹F�W�^@FU�݇Xc���U8�y�#��;H��3�?�xd�K��W�:��d�A����ю��h `��b�э��ǘ7�v�yi.e�̘���q1���Ŝ�r-v���6r3��h<���
X(�1�s�Vn#m<�뱕{uA߾����:8��o=���[fm����*֩[�^���?�Խ�5l�d�!��3��Z��"|��K���ҳ9�z?㒡]��n���c��z��.-q�K�۶����k;��]��g]��c �V����uٺϢߒ���#Ўث�\b&b��;��)q���.�/�=��g�4�[��R�b&2����Cg�L
u�&����G�����iqJ��ϻ}��è�f2�z�{��݉�=�w��'�%[ ��yw�YmPA\�O���y�
K.s
s�F�5à0�WH��)$��ZhTx�W�x�S��
o⍺٨��+|�gz-�!Ѻ�GC�|�'.d��5U�[.2_��il��K�;-�Y�[���arji�v2�S��*c�T"�h*_AZ��hu�iM��h=�7�J���ӜB�UN!o̲��Jf�?�����nM��L$�D�
�>j�$ߑ������o��"Ϸ�jg��[����Re���zlf���X��*D�����r��?!�I�dRC�m����p��ٹA�Z���D��í�Z�|�Jj)m��I�[C[�|�<g�n-_�z0m7<]�E4�4��@��&�R���e���'�\5�!h�u1i,}|[R�%x���'�6%�u�cj�#��Vo�{��:���4X���g�LT����\L"�|�Tk��j�V]o�U�"�M�
�k�O��1�Abg4�h������ZS�?�!w�����Ю֌N�74�2O_
�q�!�p'��BN���:4�Y/�ŘbI�{t�S-�Kf���%y��fyv<d�׬l��K�D�g��K�K��Y��b�����+"�����T����������t��'{/9i;��9i+P��s�/X��U�qHw���EכFG��<�s�ô8��B�H
������)��t
;���lT�h������
�G���NE^��1� �GNmaҎ�Tz*J��}W���tz��0���s��~-�M@
�/sԻ?h�#Q�柩귨�U����^��Ӛ�vT;�j+4�w1g[~^�}�k�����~+��+P�y��i�-�'"�M'�i}D�3J|�P!��T|�j�徒P�C����II���D�.a_�:Ir=ԖM�X��Fh-|&�(a�W���n0�Z�)���̥��b�e*�W��7$���8�B��\:�B$[��$N(��ǨL��ZoJ)�'9���-�^0N��%��/-F����m���=��)yDϺ���k{���sx����hA�v���Kޯ���?%��m�Z������tĝÍmS�0�s�O��ˈ��<�=�j<����O�e���Q&HrA�m��$�Y�qͰY�+�Y�a���8�lu�X��q��n�y# N6����[!F�7u	��	
���CӸW�2'�]pKGK��8e�`�B@��V�H'��MZԮ|�A>��
�`��&�Wc>�qrw���4t�o�w���{SIy�Ϫ
�����%Ա����#+�� �
AN'���Ӹ�
�fHB��DG! 
D|A�	�83�q�����ϊ[m���*���@�U1�R �IUHx$s�Z{��L��{{���}L��g?�^{���^km��R��q�!
4����� �1�Y��@�!]�r�n��@�`����Ijw�!����������k�Z��/�Ŭ�,�[��b������L���tn��%�P��1�SS{��o�|�V��c��0�A
U�o��;_`��w_��U�Ȇ���-"1&H!|�ӣ8�4\�^�U
������;�P1��!_�뭔��jL[������Pq�TM_��#=�ұ�\���),%GO1��=qZ�>ҍ��b
�x�����sh=��=��d%���^�D��R(��Xw���w����|�H91�L�!�981�:|)0ʪ�b�g5l�*ÏG"�
h|���hO��(��j�Ĺ͍D�T�?�� |&ٱ�K$򱌸3{qC$��
?O��O����g0�A��X�^�^oe`XA�ܸW�ڕ�gSa� #1	;�א��vl��qN�O�?li�4��?&�ӧc��|����B�ԟF��$�+��!�,��qQ�6�	��)�~	-���"1I���N���8v��s
�����:F���`ʭ ࣼ�9C��K�Sn�P��B��YU�ߩ	��XdԨ�!�hx
LMj�Ѵ�u��3�y���.�M�DT�9�P��gy+�e��(�$XjA�6V���Vڱ�x=+�V�ߌŋ��dV<?8�P�
�wV;�/��j�
TM�Z
v�/a�M�a���e�HWhD�Uy���Ѻ�0�=�خ��
X��r5Z\��l��~��0��D"���ѝqHw^%}&#=[��2i���!�ʡ8��@�N�2�`q&+F}�gP��b�^Au�W�k�U���*ܡ7h̨��`����jsN"�ON� C����R��E�)/��cI��+�s9���|g.7��~ދqDkK��X��g�!ꍭ}Է��7���v����5lF�]oM���`�8�`�\'�Q|�����r�!
i�6��[oA�l�Ϡ&@Dp�aT�S?NX��Wn�i��߬vb t��C�F�;B�H��d���M��S������
_�7�i螷�{Ac6�4@�
�����H3CP�)�R1H�-+�RאJv��H*+������M,/PKD^��I���%��6���@E�t��+�BA92���,O�����%���p�h뵧a��<M��҂�3��K�]����ߥh�t�]2� ��&�Gy��R���3MX���������k�
=+�T�b�~���Ƚ�ț��tr9�F��<F���'�f6V���R0�J��E��V�ć>#��^�#��s��L
0���-.U�p�AF�pAxDӸ3��B`��:�GPۃ#uuF�)x��!�O�|`�S�&�p>M���=�v��]*��=�z���G�F�e*R�8�r�wC���˨,��z��ʇ�qRI��F}�>������o����w�8�,L���_���������W2*	������j�"� �s-����vY�:�WE��g�{ć\�����I��}s(u��P��$9D?�h�����ۨ��Ef$�b��<������]�X�7�131+���� 6�q�2gH��?�u�b�9 4+g|�p.�A�f	ǋ��/q��%�!v��>~% b����f9���G�1�����
�ҿ&�I��
^I��M��t�c7�k�ǀ�V�
�FA��8 Ĩ�!����5q�ѯ��7.է}��C���?I��@��[��D�^�ꛥ��X������������~hD�����N��s��m%a1�:�g S��,�#�&v3w��r���(�bK!&L*�i;���h
����-Qhb-9�Y� �'_7\ݳ�}�J��jfʉ�(;*�T^b��ʟ@R9n��}���+�jW��m��?�1�Qr�Ηw*�KY(�P��{��C�$X1�G��U+7�W����f����XT��o�"6{��&߆�o�h�3N��������ާ]i,�;^ti���?}�.����k�o"�ox���.�������q�V�jc}q�����;��V�����z}&c}�`�q"���'����<�T�N5�OQ���xP֫�#��?�*�r?�U�c���r5Z��OƖ[l,w_t����^��}].]+�p�r�˹�����Vr��x!�8����]�Z�nCF>K��ѭ6m��;N��nSj�r���-��2���Z.�(��^��<LUx�)2Z��?�A�q=	�A�"
�O��F�Ce>>݃?s�g&�Lß��s+����������k��g���?v��Q�*47�G/��
ۓȬ�N�����
����*~@&s6:�Ho��p��b��4�E��~Z�ӹ�v*����u�K��ͩJzٽZ�uuh�ơ7I�)4�}v�ŖE3�S򠽼4�'���eWy�\�K3�[$X���q(��Y�K�����M	#S;k��lX��#�g�f��ؤmy
��h�b%7QhN�a���� �@@�Rv>@�V�R0/�%#g[`u�ʮ3���

D�F���@\r��� �y�g�&[>�?at�W�����#h��
�_Q�!jAm�ZP�ZD;�^�Z]!O.�Op3�jf1h��Å��ԯb~v��t��O�ɇn��������T$|�>āO��xژ�?�6t=���2݅(	"7ڀ8��Ѿ-M̼�Ѭ0�ʞ�<Z���z>O먷��"?u�mQ��A��`��w&��3Wua���ھE��գ�m&:�� ����Y�(����%�n,�� �n�@x�raA�K[
J�n�gD_�h>�^�u����PVq��q�E�I P�MO��9Y؄���EV��(Eh�h���������\4h���:��+^��gO��pqm���av��W�F;4���)dII5��
���42���|��VL)�U��=�E8�w6�b��Y���>��"��-ib�Ͱz
s%��w�E��ߠ�N�"[f���]L�	�w;���ލ��St��wW�*�ݘ���am�/���%G�«���Юa?>���x��!ϱ� �'���̝@���4d�����	Ow�;y�����ZI�iZ}7W�,�g�CQ�*�ZM/,we��N��8�,��ˆP��5��\}F���R�',cy����u�b�G��h��+��)����lǄ��$�׋l7�������ԝ�-�F?��h{aa�;'!fag$hL_:���*tXu�<V���"*W����x��{(��t7\�s��`����a�ь��o�:B��.v� ��*L؎�>��㫋�f�r��%<.Շ�,�1�^1�;Y`��3�@���YQ7��d�F
�����*�^�{��xq�f��#H�c�j)"9�*N(iw1m���S�b�C:%�C|��L�%0i�:ȓl��������'��7y�4���C��� `�i�&�"o+��� ����@Q:�Կa��}C�3Df�!??��f6_�_��3��q���Ò|Ly��g�.0>�T�0��f���Xܦ�S-�B%N".�ms���W�𸳳�{��������a"�G���|>�d=�t�%ߘ+Ki��G"n{��!��f��ؤd�Y��f��9�}��l�z��wx
����s���Dh�Lk�����ʕ̲4?ݤ�.�f�L���h&���o+ּ�Y(�F[
r��'Z�f\��@p�w9�͗w��|	O�
P��R���wħ�����[��v佊�q�Ɉ'�)'�?an�FV /<��;�q�dj�<�u�������=�������Uv����{&/$����cÝ$[��Ƙ��n��p�;�ez����ә�<��Y�r{�^�z�kj��Z[o���lߢ̼���7������i���B����=r�?���#�k�_�?X�W�#r��}���Q-����ޔ�gR��C)f������ͭSr�'H���b�4���!�OX'����.�����0�8�X�e�h�?��|�'n�,!�L�a�>�[�������A���)�`|��z`Q+���\�~�3��=tϻc���݉]AOgh� KD"��8�2}��$�q؃f����Ӷ���
H�r�F�Jt/��0�]��&c�����J�M�E��2�N`"ʧ�Ls9�U_�/�O�`���6��#��G��X�|֟�����}������|.(��ϱ��|&�g�9�vm>'��]>��!��J��o�s0c�F����T-+���Y4��+�Pg�,l4�(M��e3�]t��k�R���1vS/r�d:�(8�� ���U6�xٔ�Sa,��k�+b����kW�Cݭ��Ii�
-?V�;��H$�a6�~�[�Ёh,���%�ƒl�@f,�agҌ%���j0����ƒc�R���d�I'?�hc�m[��K4M�[e0�4Ib�P��m��D# h&�F����$(ŀux�%0��#&�B*6<�iSR��c�ߦ� }��?͊Y����3����}�^�z��X��L�2q���`����nO@
]e�ɲ��F�P}ETC�	�ABP�#��`F74�"�5|������
?���	'E�C�wg�1�KV�����
����P��dN�Ocn2<{�n�s����k�g�Z�q�?��O�p����{=Q~�π�3����]xVr
Ɇ��D��%ޮ�HA#	�C�����k
%y�N��b�p[|s�I��cHe�LH�Αj�z�.� ���4i2S)�,�qL�Z�/�ę�)��m��R�g��H3C'�}�Q�Љt��A���ߌW!�\�a��V#ݨ(��Fz�(��|6�88��#lk]��1�X[��
�u"ބ	:�(ё�x��r�!���|�$:>W4����!�юWp�O���MJ��-�rW�Q�א�҄��U;FMD�i�Ƕ[��U�3`����P���٦>�OQ_�L��_�NH����
8��ȫ��g�}A��_=۔�	Ѹ�M��38B<N���k�YP^20��4�Vbr�����cEXM�xvfHiD����(cv�OE`ހ`�6�}�B�����(���D���YTf 1
p�j�b�\ݮf���1�u�<�w;��
B�ޤ��J�����b��l�����O��~�䮝��߿�}��y��.,���ě�Rp����Ɉ���&� �r��gW��m�]�r�ie���<�����#�"�)��U�������d�K:ѣ7��i���b��^�{��K��{�/8��Ƙ5��{�1#Ҫ��p��}��o��h��a�(����M.�k����W	�����dy�?Y��+o��G+��k.������弹��r_� 畏ʫ\'�U���̾�*��������|5.��#�ވ�x�?+ov�#��8s�Xwp)p��F,2^�S)T�q��剳��C�ȹ�P0{ǎ�o���Q����j~h�`׬F�Z�5�ʍ�ڔ��Κ5��"�5/���꿌s�ŋ=��Y���J�<��Q�
&v
+�kAX�Z׮ve*U��M���.��{}��.�O��Ԗ�\DW| +:!e��
��;g&��O�����y|��u�����D�ѳ94���1
�wn&�.F�އ�h��p6�1�A.<�E����/N5C�:-J诤���If�/��㢢��lf��@^,�Z�7z�`��$����a0��S=5#��d�	�J�	���{{�M���ҝƢ;'�q 2���t�6��]Wf�ӿl��ȷLx���<���gϱ��"ߦ%�eyx��#�Hs
4��[8j>��PH>��W�|�-��z=:�咛�mt_;�և�p�a����82�����罫��F���֫���7q�����s�����/�!ݠ52a���FOQ_"w��"Lۀ�3h�+��[��~��ﱹwp2蠣�R��b�P�%�.u{���.�p:e�VX�\ѹ
;_צ��`�s�͐�����mK��y��ŜK�V7�Yg�8m�[j��+��s�o�'8��6yE��_�����|,�T��O��6Pj�]Y;���k9��m%3��U�'msB��E�ߓ�
�V0d
c_�n��
�T=5��o"mH�y�t��葇bp%���������NyOv�t��T�� 5_�L�w�ۼ"���ܐs���å	��'#L���E�ڸE��gn����Z��H������> ��3"�+��C!"��q�R*w�+-d3+-�N:���,S�~��b0���g*���1 ���dc3_;/�4|c%�@��ʬe�3�q+�z/�������z7;�hAJ6L��ފ��u?ό.7@�x��F���1�T�C�qNNx���
�3�)'N��v�2p�KC3q�r�>Ӌ�>D>��$�����[Bu��iB�-f�n[>�g�k�֛�O�g���s����n�&BsB/��]�"�|��V�x`���B>�`\ zA�F��F+$f�59��2�9���{�t�K)�D%9�+΄5���_��9�#��A4��v����I 6z;��=˽j��{ǀ�&��
Hy�SYE���8d�˷�(��_�=:%��z��~�yN��L���<P���x�'�r�S���%?q�J�BT�X챢S�"G�S�d&W@A#`��&�����M���>�jD��\�V�pʥ��Yk��VNv�^_�VeG3��0y�EԔ�s��I��O��ٞ"r7��:MD���E�3.������x�,6��C�c�7x0Q8��a%�����]2"�l�7_V&
�ے�@I8��#�2!lG��q�N�i1�{��|��� T�$O��ǝʜy
6G��<�>*#��"�Q��)�?��h�_vo���o��߳�%�B��6��XE4���U�K�Ҫ�	�H����K�pa�0�2�,��µ#c��!/�����	?�>�<6�B��A�D?H�

j������^I?e�`ɜU4+����l��|[����+��-���N�ws.��:o���Е�7����jO���!l���N�$j�i���C�[�Z>Q��c�]`�MՊ��vp��M,�(�sx�W\M�l��"����������R⊩c��D����8��7��s%T��*
}kכ4��))6�����P݆ ҧꭗ'��FH��T��t�"�]�>�!Qu�Gs�j�8J���zVrK�7 d��\���L]�
�O�B;��?�Q�yYk�8V�`^�7h��A(�Zs�P�=���U��Z1a�0)�~N�k}p/���,���>pV��L�����`�;��鵗PG��4&m@���VFC��ϭ��������)�/��Yq]�ٸ���B!��2��Dm�c㵅�хW���G��t�!M��Ul�L���.4%�d>��Jv
� g�_ׅ��t�KR���蔿��Kһ��F��)o�|�:._ތ|�	T
cPM:puC
 �/��=�Pތ����V��ĜߒA�Mܷ��W|q��g����y����{��&E`�@l��hJ�����\�� 'B�B8�攨�K3�_u?}$`�/;?T�4���1���*�U�NDf𒥧Z@��v� �NNX�,,e�!�@P�'Q�,�r��񄱸�����5r�QN�E��	��o��G��`���5�Q���6�f|�����(L.!��	��
���
��(��m��F��^D�6S�
x�&R�ƌP����k�\K LX�@��5�/1>8���B�'�[���$�秏���x�q��=on��s��]�Wڍ�}\Z���g!BuQ�^���y����0����>�׸N��������G�x�1/�����k�����\����&-_9�a?��+s��f�Uƫ��_[�y�W�e~�mjm���6L�s��*�]�kw�S���V{��`v*�ٛ�	��E�xu��:�e{����;&꽈�߫<N�Xd�ۙ��^^� ��X�^�(�5[�.�����H���O&��2m?3v��S˯8v�)W��A��q�(,=H�l,�,,�����|m=W���Q�x���pBW���h��=��� /�!��!5szu��cf5w���m��4{ٵ�T5!�7�ߪ>��'Ap��Ph��(
N
��1כbz�䌒 �E�\���� ��1��H8�̩��r�+�)��W�
�7�_A��a"D���lU���{fz�C��{�$=��^��z��ޫo�!Q�*1kڢ�S����^s
x}���X���:���t�N;R{���TS
h������������L���9;�&dg�b���ny�
c���[�����ܑk�X�o�fS����1��f�M�a�.���qQ�ޖ�߫�(���XE0�'A�a�Q܏�_E�|n��{�O0�{��r�^�~����
8�=8z���y�i(?�Z��9-b��	��N��Mz���k��})�g�<é�~N���hE�5��#���y�c�X�w�&�5�Fz:Fsrj�����b�1��n�pEjMS:�E�G�D=Nc`�?������)a���F�D0��B�Y$��؄��bF(����P���{#���x"��=��
���U�����p9�L
T��סX7��{���7�ќt��d��r�1����Mĳh�^��r!3`~��P�)_�[�.��F������^
�h���B���H�� 	vI�$��p��F[�B�$�)�n�\��כ��{}	Ɖ�t<�2��ᮡnyV��Gw�Ehwf\h�[�vgƅvK�W��c�q'��
\�aY(֪�&�v�.ܔ�^C,� b��E�
�Q�У���h��1��3�UW�lO�O�j]�V��,��_iq��si<~����/Рm;m�&�����8'�v3~�\^PJ���V�`������&��U
���.|t�4X���Df'�.�-�����׉�b.�]�v�ΰ�32#�.��zM��x&�j*Y$W�����_é�:�d��r>�ռ��]��\v��]�a׼p�]j�)���>�p0��r&M,攳�+m"m}�\~��1N���C�>��8,�s�W���ơ*�nIbݒĺ��Z�_e�®�R��j�F�Q��H�_�Ƃ�l�qX��㯮a4U�V�v��&�!�sR,�U�á��8;3W�/���\��(hL	0��T}��S)c���[)��.ɩce� �%}0y��'
Kz��2z�O@�_�AO���9G��(����`�M1Ӏ���.:�D����uw#t�U�Hox�
��y�<[�@N�i�"4$��������B��򌂓BV'pY�`���$;BrH�{W��\��(sy��5�'�?;E��Ñ6{
%�u
D��~�b�9L���"�� �kݣ�I�.s�Z��XOA�}���]���:鴉BHЍ��̕�S%�|�Ϗ�Qn�>oˇԚohr�])�?���1��-�^������{���xï��Ǘn����^�d����퓋$_p�pOB�/�y�X�Γ�z:�j��@�y�,?x��}�}`2M}�s�Bê�;�>B�*c�̽�|GU;��r+�XUwe���H��ʧ[�H���XәM�2�D�i�ڦH�����9�{e,�f��V������7}ֵ�8�sk�1縖��iԔ���
��F�%W�*�Oc/b��]@�k���{�"_DA��%E2PLCan yPM�Ϟ0��J�Y]��JeUԃ�Z�1\��h��_�ƮG[�����;����n����ݱ��I�K���?���[�/��1�O���=A�<�ƹ�� 7}�31�k&v1�ߙF,��/`$�`����Z��?��s�K
���1���=!��^��h�=���6k���A��t�t
���稭�s3��zgH�)㴣�A�)g����ꨪ��t�4:�~�]��ڻ��Ĵ�d����4�c4��,��y�g�#|�n���y>��AT��Ձ<�폵�n�cz����-�`Og
�Y�� ��ٺq��^\>��b�o\�4�w�����A�1�q��9�o�K�ǖo.ͷv%ͻZI3˻-�'?��`O��yϾN����]�s�!ϔ�2L�o}��c�y��y.!yfy�^N���o�![L��^Z"y>p�l��&I�\b��C���~�!ϵI&y�nҩD�3�<��{�-�eB��$����gI_'�u�59�\�o�J�moX�h��X����z����udw'r�fo�rm�;3?��=f?l}��c���庌�i&�	���MzE�ۄz��a�\���a�\�v.��.��6���=:�=��uI�\�@?��n�����~#�y�6f&��d��w����� ���׺/��r�>���r}��N��Į��zT�������׉���\��}��#��޳���?��q͜��Ǆ����M\�l��<O�։<_�����l�۱?�g��O{ Ϯ��|���%ϸ�Ac�q�=����?��r!����r6w�O��d.U�j���օ|�(�H��,��V�1��bߪ$��)[`�a=�L��B�
%ȅ�%U�{FQurǰܴ)�aie�a���*�cآ���~�B���i��+�꣗W`����f����KA�jh�xF�����`+PY�&�E� �TLO�� >
(���}��|�evo/����^[[�u�Kzu������`�uE2W҈sd7��S��e���:|z���w�2~���LI�Xw���`�	�		������a�(y��=���c~u���K��2��C����cIZ��_��7�OH��a+�}�M�/ҟO?6��{Gx��ֳx�_�f<�¶\b"B�۽�B/���K�������2�g5���?QhJ��GH|^S�R�<����Ra�?�1���m�|8}c���6�ki�~E��On�a􉈱�o��&��X_dz�L8Z,d�W��'fh,/#K$�3�wi�I�؉Ċ����m�˦�����[��S �����)��ZvD�Q�=�CbC�?�u�C�}�R���F���Qϗ��#b�q��1�
�M$_�F[���;0{�:��q©�T&���#U�^_wjؾm��BT�J�����xS0�������؜\���A����$�n�h��2����Δ�`����}�T�u�cn�����<L�1�?��pw`N�ꛯc�G�X���-=���q���]5�e�=��d���):<-�[�����ϒ�lG�����x���;�:G)H� �~g�R��]��s�+������+�Q��Vh��VG�qv�kG��_~������^YYa������%d���o�ɏ�����y��l6�ӧy�ZWZ��c�9����I�r'��,��)�����gqK4]t�鄯�AG���]����_��	���6+mhe��cf��s� �V��m�0�)0���NW�H�h�ӗ�p�%�&��'���'�H�\��U��M|����d���뢰�bG��v�Y.���xa��"v�v�^|�.ځs���#���מ�jƷ����4������2�&ɕ��G����O^$("�ԏ�л���깄$Y}��	�SD�^l~&���Φ@[�m�]u�������TuT�#�v��MK�7�Lc��I���E��У��陵�!̾�{�ǎǒ��b�}�&Y��Uz��RLEy���WV� 
���SU���V�:	r��X�1 �Y0nǤ�ކD%}I�/׍J����ψ		�(NV߬�YY
��z�栒���ۖ'����=�4���[��N���#*�����#�|��� ����9������zd�.��X`O�*���s����Cm�C���X�P�*���&�*�׬��G�{8�9=_��`��0�W	�	n���2
������v���w����=��������H�I+I��z��T{�?�QZ��_�*gkz�Q9"��%R������u�y`�.
���>Ϩ�f��a�Dq�!���&6�y�P��z^��בw]��y���f���]ṵx����.���on	��_�`Bk���!%Vq9Y�k�(��Ӂ<��7(���g_=�4(��@h���,^0�Cm'���J&�l�SX�{
�
�e��d��1�/��4��Z�y1����.�p�y�O��$A��W� B����R�xH�ɫ�C��G�N�A(�)[J�����Q#0':�:&�&�R���D��+�4�
\�̭�� �r<��
~��v��l!�Gy��q~I���v�*�N+GB�W7��	�ň�h-��-�A�(�`���p�sc{�!z��7~��뾃�y]Y��4�U�hWo�`3�ϵ�ׯ�
�x�v�0i���r�+f���x��e2� 7������;��y���[����C�����K�<�l1E�=���n74���6�8�66v�����Z���ȂtZ����0� ]C�5^ÜW��jXp��P�</���[�k0%6☴R�].n�֖�Wxʲ�k�D�7�l��Rݪ��UT��D�
:�^L
ϟA�~�.�ձ���j���x�$%#ĺy��GGl��2\�H+!�g/w�SƈK�	�
z�ۨb�Ĝr��#�j<U�p�kg2��$ʘ��d�/������w�?:(r�����aV�A���M�ߙ���q&am	���᪏��d&����(�EtjG(~�W|رgQo��\@��KG�%$��W(sL�礠���E�����HP0wi`���"	I����|��:4\�M֍G_��q�����j :�O=@G��M/&��0~;�M��c��4�����Gߡ*WT�T�W4���+%Q���W)cO�pf��b��U)��yf>xV
M޽C
Ĕ�w/K��D��;�$�Cʥ��_
�74Afz��qE��l���}�m@���,@����������3H�JT^��XQyA�nV��&g?Ǥm�����"�����7����7?��������}�������?[{?�S��xi��;���a+F���M\��ڿ�������gz�w��hL5>�_;Ӫ/�J��a�W
oͱ�.�5#����ƅ��W���ɷ�$���C���.�+�X��*��]ܦ*�q{�l��ɣ�^AҌY�$M['[2�.�^���8�ԤyP|�z�5��;y�
���a%1͸�j�&��9��=L>�+7<��3G{'>|S����#}�P�j���^��*L�RM��M�?ޥ��2��Y�4-F~�0>����{����ǞfPJ����������\k����.�����w��_�����֋��S��?���{��teKt|���<�ᦒ����k����m�+Ow��W�Pϲ�p��	��h?���x�߀�O�����+���~E��O�?G�ꧺ��ŭ�+<I��R#�A�����L��ٯoa��o�����pa���(aqySL�?��k��a2�#h������K�uޕ��I*6��'��(v����V���P)~1��b��L�	J�f����Bz�a�D��s�����y���I�Pϳ�K���H?D{powD�!�Fj�ܾQ���
�?�����k=��鯨�Kױ�\d������*�S���:��_8'�g�����4��q�|�_���w�I�+�z�?���/`z)Hob�N�5
��I��O�_zz`��J�����C��j�����gޝ�xf�K���6�ܤ �w~>����,��,�����=M���6�������$|�����kc�H�ט.�1����so3}%j<��Q���Nx�3
��y$���S�{0ު��_ڸ����u��z�L��1Ƌ��'h�`^ZF[3�@�l>�[�������6"����F���{P�>j��^��o98��w^���r����k�OG��K��� XJ
�x�*A���0*�����V�wg����`�O�;�-]���T�ܤ��Nhk6S�/�C�n�-�;{}QȰjnD���L����z������P�ݲ��/$�xk �>ٓ��~�
n�b��
U���,-�^��!�ի؁�g�`9܌�s��PD,PPd
���Pd��l�Y�a�����C���E,$���ߧgm�����W+��F��I"l��0T7u�0�C�qaS�F�[?�kܨ16��s
����� +���5�8!Oc�V.A<y���8�}x��@s�o��rgB�VM�m3�-_ԾĐ�����8�W�W&#����
��+�!>�m �7����_ u��Tƭ�"p_D:�5���'Ko`�����e�_L�@;ݱ�XǮ�����,E	���ytmfX�~���/�T� ��p�/1�+��nn����
}�v�����a���Y��sv=!p�K�}���*� E��|u�jn᳞��3CZ������Z��O:/-�]�Q�d7� �eK�xm�]�����|��8��p�۬�_я�_x~`�U}�Jk-^P�K�|0�?��s��M�[��o���Km� N6��H���l����K!�d��6za�븱̰�;�a�L��$@F�# UD��lh!g>�������-H_��Sؚ�'���o�x�8��Wu)7H�~J�&1g��Qp�2nЃ�����AO����fn�ө���ܠ�+Sb�,O��(u+I:f����ƠÒ�ۃ�Qs�p)@���|�1Y�3�g`���r���ޏ��::V��`��1z�7]T4�&"h�F��&!�A�'�Õ�D��	����/z�w�5�w�N��K�x�n���Ҳݟy7���@��$�@k�;N}l�+�H
`t��W��fO
R�3�k44�Z�]ҡ�X�gW�&o�g�V��fޭ����Juy���
h"�&�')�u�k&�"�ۤ���[�G�j�ŷ�O��d�e�]	Xꪭ�=��)��B,Q��A���%
7[¤�g5s�,l$Yx�d����n�����N��&���qIGZ�Q�!*v{���]���1H�ǈ�Q�ef͌���s� ����Q|
Ly����]wFTm��]����,z��@�!��@2��nr/=��S3��T��&��/d�x��?�D˃��3c`,�E��><��Bq�-����x���F�?��9jȑ�9B�rؤb��5�8>�e��܌b�CI����oQ!�8%A��n明�K�D?�����zO�4}� �mB�4����=��lh����=~FO���&=I���IMd.<�|6$=�a���!i��kٕ(�o%��y����H�hCі�l��3xG��hT�E�5��1
�Ǿ�K�wăM��ެ��)8�����O��DU��6�ڍi�ܠ����L�rÁ1☸B*0bC�ɕ����D�ˋn2{����==�#1�WY������0�����E�"�"�S3N��h9#M.��}$	�3As
ڤ��V�+:���0AQ��@���&�_4�/d�#����|E�
)�x���iLØ�������3x�!�g�A�2���？�AXd���)L�&��n��S���n��J@/�N� o�=����y���.J9�D�2{U�h��p�A~�;�[����g�����-M���~n3�X�7�ϩq���?5�;�6��7Y�50�πS�*����c`���qYC����P#�L#���f�D�LM�Ic;5�a�`9��E�.~a���A���`9��4���9�U6��D�	�����x��CT;��K�{Њ����݄�5R����8���M+��5�Z��QNc3vz�^gŔ8����ƃޑ�Q���%����j=sU}#�e����x��:�`���MJ�PD?�AO��r�q���73�Y�p
ف�Q\�M3�uKN��tF��ϸ��&��LX�-Ly;l���k(`+,f��a��䎖r� [���,4�94=�������e�?��Ml�tp�b�,����+y^}��r=H1���,�]��TL��Χ����ml}���e��)��.bD�m�RZ����~�<s�����.=��3�s_����gƐ�ؗg�����Cϡcƛaǣ���ɼ��f$/�j =�80q7�]W�]��k����d��;����-4s�����X�3=&�Y�[�s���� G�|�\�ܚ�q|����Z�1��_�#�)#a>�K�x!�8��R��z�[3/��N�h'����kX��CjcC�2��͆(�h��1��{hg������)�N�^��犿I;� Na�dC5.�Ü��haKn�#<z:Jy��@��H ��}M�r�q�O|��w��Q>���.Yc��U�ы�2���o���ǂl���qb�r &���ӵ��㸕�b���C����䲚|��}n�^���Ƿ%+Y�,m�4���!�wX*L�[�,��?Gy�wz��I�~kKz��Slڠ��x�eK��Q�hn�v˩ڻ,�VH4���8�i���n������h��ly�v��V0!t�f�!�3����S�;A�Hìf��o�
IL�G=h@π�xMX|��C��
*�-�b�+�V�.y�̿��IB���i�x�;`��ax�B �����x~�����J�|��TR`0�#|
��!�����0�^�A��L�G�Q���&P߹�M$=�4QN�\��:Mt�Pb��F�_p�������2	�{n�^���E��@�zNm���l�ߒ
���R'�5��W����P�AJLz�'���1��~��gxԲ�0v��T�62.�J�@Q��r?|Η��c�1��$�&�KK̼?7ze��aU`�T�<�V�2t�}��Ľ�St� ,�Hz�Rt���)�޾_˘/�W��C�Kw�ksR���ks�s?��K���jϋA��s[��vh�w�Y��&��|9�ct�!~��,�g�Rax�g�س�J�g{�OJ�)��.~8B᳈p���0D�m�� ^/�?���/�E~D��*���_�3H½��E��~uN�:oW����N#�s�R�j��u&��tfx�U�5��<�,HU����	���'L�iz9���Y`�$+���"�6LB��5O��=^�M(g�@_&��NO&��	��{:�P�4'���1T�"��]�"�O��O���K�,�,�x��<4Z~�xH}�I��~QD~}�G�ְ��V���N����6��P��胾@��&��c�My��,��������r:��^�V�$���m�*�R��`��%�Q�_�r��&mÕ*Q���b�tW	)��WK.�)�i����o�;����A��uy_EW����Y��䍪�G��U���iO�a�GD�eF����c�E*-dd&y3����� ?>�)��7�'�Ik��S���"��;�H�kĥ���>)osj�;�Ϋ1>dP��:r�vQ����Z�j����(���f-m��d���(K��(}ѱ2[+�����$�a�1��Y�J%L�nn�^�_�/.d�+�>��а��V[ض.�ɔ2)z��eS�/i�`����*(���a�xů�c���"�G�4��v�ȥ��S� #<�*
�NB�ø��1�<���:���z0t�gT��<�@1�A�ZK�ɔ.��!���L�d��=���~�'�,�� ���n������_���8�`������ԣTp�1
b��%��E�y�V�z��(��3���C���?����t��_�m���w���)��n�-5�����|�Wә���b��e��%�9������Y�f7e�����pyO^�{sat�ͅ�&m/)mg.��V@�#���ExM`���v���{P���ܤ������:�5���ï��t�o=��4[䥵R��+��/k�^O�w��e�����d�W�,���^�]*�Ġ�����u�p>����:��V����6�=:��#�Y=���z��R�ף;a ��ߢ��`<s�-�=L��͘T��3s�G�ah�O�� �(�O�C�_��{C�����ς��	�X[�-]�8�h�t�7Xd�qtgp������ ���څ�Sh�4�I��P���hM6.78R:���r�4�$�����~���b�*N���c�i��0%1��$�ՅJST*��+�RZH�������\+�M�ȣ�
��y(�xn�ͮ��P
��$�v>�ސ$�O#�o�~���J6`1��k��C�h�����_3��yQ�m�ގ���N�H�E����Z��j�oŧ�-۸~��/�{K(7�缸��r�y2w�|=C�PD:�x��p���~:�M�x�yfix�
)Сr�Lp�qX��s�K��:���E
Ȱ�k�8$����w�<k�a9c�b��Pό���g��	V��/�W���m[%��lo9�|�[�
�{��{���sII���S�uU�&�̖�#��2���
ª�
���ʢP~�����c=�xv��p��X������� @���~o�y�i��d���Iԁ�x�$�3��[`{��qk
S��ȕ<F���\tb]��'�Ц�6���m��"����BF9
�#��IK(������6�O��J����c�-�5#�$y�!Q��I��k�����{�����v_Gr�e��5U����J��/Cr��I,��h��0Y)_f��8f�|�lU�����/��Y-�k�-[j�&T����[l0�m��ʋW�4Ѓ����5������ u��%2��w|�]�D~�/m@��GJ�G��x�pf#3&�^�{��ڿ�?0�f�>�|Z93�|�:��S��i>M���1���#�P�P� 4x�d،���M��}d��<���vqppIKe�O�E�u<ǐ�	��g^��it��^��&^��h��������]��F��qO�Ay錘�3���_�_d�&�o�@��]�L�K-��3�_Bs���<�Xk�,L�0��M�uTe-��Yך��g~�@�4 S�L��a>bΗ|�`��cEVh��`"6���j'�)���ɝ���]�e��ޟ#S{�x�߶>�!O����</�\��.x>e�u��|3��1��s?&=R������ǌ�s����^ѠL_{G�Sҹ(����ӑO1�
ݦ���q��)�iHO"�

b��r�F�p����.+�X���Į��
=���@&�T�<iH���/c��T�S)z�0Q/]�v��@w��9�MPf}�N]/aɧ�bxMT����c�#�E���=�v��`��� �	�T��7���4"�����1#��1� )2ʡL[\P���L��E}�gQ�d���<W��.P�T�AA���j�R���zW���;0<4�\��__Q��~t=��n�g�|A�}�R�܅'#"y��vn�G�������PG�^{�����(̜�]beh��K>�[jҁ�n�s6`�O���C߲dE.�-�;`GRQ2�;�)
��F
 `�l�j>�����k��.�jvun|�վ��~aW��FXvO�s� c�'%�.3�8��v��WwY<װY9oc��j����ӳ�R3Ы�F/��e(�n���^VM`�#wK
K=����S;�L�`����c�_���@h����)�bC����;����0'��$�|�P�0����̛��{@y/źK��v�aZ(u�rm'D�ߣ7� ?h'B�p;
�W���9)�*݊;��`�U�o�޻
� <���ݾ��Jɷ�_գ�5՟��Q������b��,_�i�n^ �p{p�v	�]nNi�Zx1�=����d��g��=ZA�JF��~6��4�҃,B���+��?� d0�-�>l@]myȏ#?
e��.	������F){H�V!�*?qB*���q��z,G��ϡ\�-��-F�.��F
w�t�?D�pe�4��x�V��k�g3��+ޢ�+���j#{mN
�@ʆq,NbȺ�i�͓�
*)$�!Ue�q�X�a�H9��a{��/��M�1�� �Pc���(O�R�w����ɠ٥�\F2�;@�����d
�`Ho~M�if�𩊄�Ix��0��C����d�Q_
�Ek2�nm�p�<�I�6q�� �T(0O�L����r�1�M*5� �����IEŸ�$��F�x�A��ܼJĔ����O0\j�
���)K��\)Q{R{���f3�U0+�t����B��Ex�Jɫ`azL=����FO>�^O���ۏk�������=�I�b��(V�Ӂ�S�D:w�?prD?\D5�&�*`�.�08�1|R�6�[]��ٿ�,�
K!Qy�6��M�$�:�@A� +`���&�2Q:�el?�y�O�
��P�4#��l������4��Ȝ��^�&��'mBQJ�����t}��)eWD��ʍ��P�/�$k���a�u�r�'�a,��fA�N��R&s�<�U�ffCl�f
��nR(4�IڳI���GI��K-��?t���3j0ͪ�"�e��� �ȿ�����q��`3�E��%��͂9,WcٔӚ�ĳu-�ў	$�<��\�̋fq"Z�2T�@WHz�T�	$(ka����> ��k!M9;�e���N�k�a��̈́�p\�_:���S�5�
�<�����y���8s��.5<��?�����*9�O��Y�5�J�&A�_����u�Y��+�o���7�s������[of:�A]�IR�N�j�V�t��i� Xl�d>Ý�XWځ�Ewr�Y�X8!'�^x"\�m���$�yߩ���`hw��`�k7��X`��B��B�K�!�,��c(T�Q����-�{#~�v���l����������z��c��zT��z,f���a�_XBZ�"�:�Y0�!�
iiw]��W��fn�`-������-f\�W|E�P5��$�0�S@m�� >AfM���T^r`�F����)מ8%]��!����W�t����}�t���^)�KFZE��4�� �/�-�4�M�a{y�C��WP�K�Ry�A��rVY>�^����U����%q`��1� �b]��k��@��1:Rf��a&�.E!`f�C!`�!`�_�>,���AA�wh���0S Z�b'��T�[v���#�Aq����
�E�4� T�@�5l?�,�ai[�k���tMx����e�qa����>�KB�3�w>�wCqa�<e�a&%>��ߍ;f9K|ا�"��nƾ:���M����#������������K���5�� ߲�//�61�|&�8�!�͡�a}y|6Ȁ0|V[v$N�ӛ.'�]��?f{���k�^p|�?ǄŇ�s��a��	�yv��ƇՌ	�+s��a�ǄŇ�������1a�aߎ������a�a���������a5��
M	K��1�F��3�/a��8�O0N��w�إZ�XO
h�?O�����s�=^��]xߛL\P��jf���5�ű�د�x��h����Үƻ܃h�ykJt�KօĻ��x��/&�e�UZ���W�;�eJJT��䫴x�iW���]� ���&�M�;��X9�
�o9���3��m_���O��t5W���zz`�������W#J���x�auq��-mE��S"QZ���y���ߓ�Ż���{���7����P�5Etz�O���E�<]����;=�T�^���n;�O�#||N�ʸ Cא�!/cX<�ƻ��P�]���`��wyT7���?���f�7��x�}?���RjX����_jcz`�0�"Ӯ��}<.����L爿�"`5����Ȏ���r�<fM�w�[Ã/6����������s�ε��|O��]��#զ�lU&T�N�����Ro9�4��֛�0ԞI�,9����Z#3{E�Y��Dc������I������xw��.������[t��B�p<X�L	�G�<^���K ���>f������L�x�@5M�ě�x��^� �l��������T&��|�����1����aEz�x��:���)On�|��r� 9Rn[ρ)G9��{?��ۥ�r�#�\C���Q��Q��"ʫ{#�Q�r��w���3�'ǖ[�7�q�?P�x�'�W��z�7M�����O�K����Ҍk/_��H|���3���k���[��t�K�Ά/m��/=z!�қJ|]�\c]$�t|��5��?_��/]��?sC��I�to�����]��:^x!��zVnz��҄P��r���yP��"�_شR��R>,u���	D ��b�M����*��>מ_�k S#̭.a*�țN�R�6���_���ɯ�y�GL�����iIǣ��i:�L�����ON2��'d��
2Q65�DKeꐦ�E͈���{���x�u��vDm���\l�%����w�/A 
Ąݲ��D�L��S��" �M�������9�m��9��Q �?�ѐ��E�Nk�4H0K�w�J�����_�Oy�KJWpI���v
�V����1�l3��w?���-�h��ϸ����.Ч^31Dꎉԋ�&j���I"���Q�Կi�T�uv���~�9�<�<�<�G51��7���G5��k~tx���\��u�P��g@�0�i߫z�O�|E�D�K�}ؘ̫���#��ğ&/�i��_��&��OSς?M??���ǯ�I����O��"07G�k�SE*e��B�>
�Z0v��á�B8T��Fá.��8�S�c���C��߇C����O+��Cݜ�� i<� (zr��8�!�š��\8��?�q��>�N*%�Mc}��K�8���$��dMa����z5� $�`�F�)�_�ل?�m�p���D�D�ы�������)��@*V~����ٌfO� ��xq���^�дJ�+�dh�m*���iI�������6�:?3�V�E4�d��է=�-��O�h�7Ch�}����F5dRE����O���Z�hB��|�Q�դ�Qo<�@���G��Z'�����^ko�^� u��wE�<�_���h*I��/��Ц�uI(j�ھ���"e_�[n|�P�oP��0bN��(�M>�?��Yo�5�)/Mޜ4��a�y���3������XF\��n�(���O;���a9�O����e�H�p�&( ��?(<r���X���Me�ß��z
V��P;Ud�D�Y����R�\O�O*?s3u|�j�Ǡ�W�%+�<�to:��7S͏ e+�
��6������u˗cٹ����0hi�-]\�>-�OUhig(J���Ҩen@g�2��-��̽u*r�[q,sτ�K_��O��Kӣ��R��L���M@A���_:_]�|��٩�`��}$B������|}��H�)[�i�����:r��l����}�V0m|/w�V��Tb����Mzm~r�z�$�c��2��`�K3��;��(?q#C���7S����ސuX<��\2(6����Cp�ca߿�:"��L
]����N3�����x�*�����*����傑9�������*v3��\�.\�4��P;�Y�����c�),�B��*oy1�^�4��9]fOia�&+�4��(�<o��w_D�jS��uW��k�U_��;��v�j���
gE�k��&�E��=H{Q�_\�O����u�"��pa����)u��x�Bz��2���\�Tu8u9U�%�P�j���Z���*���u�����|�P�,*��\|>�(�+��V�a5Y=�*1��)�1�@�����c��)�
����Ď��J���[sg�ȟ>�f�a��$��.�?�h��|�0��r�� �C�{^[
�e����Z\�r�ݑO��y妧��~^� �T�����f��+i��JXs������t�>K�c
�XM=k���u�z����e.�}�f��/t9����+�1WUB�.��V�C�U��O�E���1D#/r�G��jPR��8�T�rSR^U�oR�z��c��N��u�͏��*l8H��\��.*ETr�D댹�i.���\�9	/��Bﯮ�e�g4�a��������_RV��-�r�]ԏ"��e��L��o�UE���y���R��{�Jٓ�i�Bh�P��ŀ��Z���wV�n�y�c��I��/���a�u9��歮�XOU#�Hs~���
(�{ʅ*?���f��[G�Uzf]����b�1�I}2�0�O�6�fs�F����"/�&��Ȉu�l��Eo�Me���X8F9ְ�˵nj��h@)6�˝����+�vYq�BJ�.�L�eUl���R��hJբJ�b���� ������RT5Ξ����fOY��	h!/б��:����z1�^�=V�f�'d?�i7E�/�����t���C��]$�{Z\�tW����8)UeR�%��&dM��B�2��UYX�@����[��~����8b:�B��L�su ��*Y�D��T�Va9�e1�-tU���<��鹂�� . U%% �ah���W�g��MQ�,�֍P���#�~:2-5u��彺���`��F �F��J_݈boE5�����eX�(�@paY,�k<�s-�x�������+U.'�+�t���+h!�p;����`��m:�Tn�
�<���԰ø�����aO@��i*��V�Fγ9z��Y:&��$�����h��ϼ8�^�QVI?��=��M?T���Pˆ_R	���\���]T��!�ՁΏ\��A�ׅ�����_�.\�g7C?�X�T,}.\g��O�>�s�L7<�颺�8��L�� ����s��i��G|>r��9ʽ������8��׍�	^�v�ՠHF�&�UC�D5�Sk�Wa0睮2��0C:�y�5165��&O�Z\����S���"g�p�3�|��j�B�1�	�����n-V�(V56�kգ��0��ش�ذ� ���� T;��JG���U8�P0*B(��g���*SR�{h�,�Y�j'���
V6yz�����S���<o��؜[���=\k��n�ex�^}�{���6�]E�#�h�(?TNqA1��9�"zk�ls�m
X8Ew����Qӝ�`G���B"�L5]UR��[��e�`"EYeL(G>�t)͆�ĸ�~*��fF�/S����(�7����uc76��T]�)U{�H{/V�{���#�@󠴰�ډsm)�WBת����y��%��Z��:���Cm�ưnsE���v\�-��D�
Evְ�3&�H���Xw�Ww���E�_�O���r�T�%��	���F�����ج3�s��.S�oY 
�ݖu}�9��.�S��Uݼy�u#F��M���T��)x\��U:ݪ/�r�Ng�H,os��SL��C ru�o�$��[^>>���R�5^�9JW��֛!��tx�b(0��g�Qr#�y��i�М[��e�*Wn����Ԫb�ٞ��3@n����<<��OI��X�Ϭ�����2���UEW��~�2��OW�3�.���N���X����k�ٻ��,YW#*QTbPWBTTTva�
�~�j�9���6y+=����nhck�6mf�v����ؕ
}nQ@�����G����M�-�.ta���0�.l�|��-���Ļ�~~5\���W�oY��T����9h��Ox��V�.A�;G��
k�^ް�ϪW������U�	����*�������8���P�`^�b�
������!�v4�z�K�ݲv���6m��ܸ^Rb���-��i��.Jd"vdEm���o	�5��[��M[h����xM��T�I��̘���߶��F���l�׭'��V(��q߷Q�(·�6߷�M�&e>���P�긓ik����	wo����&
�noGC�B�z��J5�6�������h3+B#�+��%�f�Wc�(X�n���xH���2�����5�|q�U
�Q�r`ڤ\�X����n`�2�^�/�~��J��߀�͍���I~hc -k��{3� ��;��͌u[�2�=c��#0|+cy�����v��~ �����G���}�^��5����'�pxX��I^�@�̓y;0z��� ��=���2�:��0�/s���^$�0p�[ �^`����ʜ��c�q`�X�{a��2�Ɩ�|�\��9H�r���HN ����e�;
��<v�W�	+e�]&s7�)g9�N4Co�S^����>`p��xZ΂\`.0t#�r`/0 �s��<,�c����^���2o��!�`/=�!�C�1� 0�A��3�c�0�.�Q`8At��;, �m�y)=�=���oG�o���h?��H���`�L<"�����a�|��p�>`>0
,���0����ہc�.����y��<
tG�e�	���z?, ����0�� ��Q`;��F����!�a�p8�<.sv!������(0 �[�C�0p�����!� 0�|�q`/0� ��C����م��ۀN����2����!��={��v���<	��-!��>�!�ڋ�N � #O����/��������%�{��~�~`'��4�ƈN ǈ�e�!�X�=�z ˢh`�W0�.?0 t>�v�a`�9�8�
��qM��C��s�K����x��ǀm���'��������.� ˀ������ ��P?z敠]~�~ƀہ�A�p8�=.�3�,�
��Q`;��kƸ!�Z�0r�c�୰� � ˀ��lƀ�~`8��'�}���?@q)�O鷡��N�����V�snG}�n��#!·��
�����}�������<�g"�b`/�
��&��{ ���VηЯ�ȷ�p�
��ƀ1� �8�ǀ9-�'� |� ��{�rf�p������c�ta=k���ΥR�3V�����L��;�칵�����dן}�%K
.��-��I���Kc#H�VGy�*
{��F��8�1q���;�Iҳ�,Eg�n���bUgz?� �|�v��˪��
*�B+�Ee��eo���]�e{m�+SЩܝ����e~�Z.BQ��.zA�f�Cz�v�M���*ۍ��F�W�����l�?G���6{�G�]�92����:�9z�2�Tˤ�qH�@���ۤ�B	.�NH˚+�JJ;�v�E����wX���mf�_��հ�v���姴;ʿ���2�����=2�g���ЃH+ϕ�wL��m��av��Y̛L��*QJ��F�)�v�{NQ&r�0G��ȼJQ�"�����s��W%�:�Dz�vt#} �g��(��}���g~��s�c˯�C��@^���T�򤳫j�1��̜Ұ\6�^e�J����2wdD��,��OH���x|��I�<�2{��O&i��Pƀo_���Z��^.�����x�V�D/��Ε��&��vP�l3W��jc��&�՞��iL�����d~�)>��W�ޔ��T��|�_���K��o�f��+]a��'�g��O_>ـ�
y������t�-���|����Ó��6�j���Rc+�ڿ���ۦ��9j?�O�өo�7(w}ȧ@'�|�͠���a�Vt�c2��Z)O�{���^{Li��7&���[��^�����ej�X��}m���ԪU�D9������k�}<���Ke�/�U�j��w��ڵ�s+�Oj���-�Ě�Y��u�n5)ڭ��-�?�8�v[�5�n�R�v����<���K5_s��j�ߩէA�'L�B�=��n�D�ai�vuk�Zkﶚ��LӰ�u�>���4���o#��j�M'��9?Vc��M4{�15�ź�|�KOd���L��4M�B�::wf���ǈh|[���⚒S0���Z\#�?hA-Z���Z�@���l��Z�$��ҟ>0���m�n?�ʻ@����M)-
�o�S��GX���;j�Jv�*�:�F--�"�G��F���	w"�S�[����	f!��n����J���hN���aA�l��u���!p	\�������t���COj=_z7M�E�2�Mk;�_�k�1��5*M�T�a��F�7�4o���7�s�B���iS�[;���� �-"�Zgw�+s[#�9~��L�ǫ�ƛ[��1��@J�u�v遬=t�`�˪N��.���id���7����hc�ч�K�4�Dە�= �*+"�ն�nV/�=˧̏���4&b$��A�2����Ә�G���!�|Zl|��i�����sE���aJWE�4^oRe�z?�L9����{O�	�/zU�lVF��ݖ]�HƶL����pC.��1�ȱ�����׶k�*'�%E2vYw[�0��Ղ(k+K�W�Ffa}��TK����`^(^-�S��z��.��]��Ҧ����tU�k*/d���ڏ;��A���-�{O�ǏY�Mi���2�.ε���b������j-��Ok�&��Bz����z
[Ҕ}�Vv�(��]���A�ۚ<����
�����1;��hYw˜�r&���b����{�8"dw�*�^��N��-��։��,M�ZI�tgr���G�ݬ���cS�\=ƽ�f�94�'���S����i�,�߳�{�XZ�e���BB[O�@1N��!�7l�>���v�M�b�������]����,��W�n�`�A�
��R�SX�h�\�S�E��:�"y_m/V�ՇΦ��<W��i���(ņݐu�C�6��6�n���%��o�����I���`����-����ӵ�[?V�g�[N�9/�����yI�+�ܪ��F��@��� Ω��\�|7�E�C2/Og+��bi�R�3��]܉�I��@VA���L��uu]���d]�A��Gd��im��_�Z~��������g��Ge�@��Vl�u���2}�Z+h�����&ƭ�@��ɣ5�͍���v�j4(чA?j���q��@�!K:��GOݥ�b�F2
΅��1Uv�]:�i �;��ۤz{�C�궺��g<kNc�אn�ޜv#=͸hN9.^N�+�>�%�߮;�s���R�$t_!�"M�D+F��K]C�t�����bZpT+g�����E?��6�%��.[�)~��(�nz��2�I>���߬u��G"O?�dj��I���m'�G����G�����Qmh�/'�z@�m�~�ZTG�}�~к@���{=4��h���>V��ͩ�Xne�ҁ�e�32�yim�, ����n���ˑ֓"���5�!�C��=Q��<q�����/�ڲ1�W���h�r_EZ0E���I�h�d{tW:ڽZ9��g7؏��*]��0_̐��_�o��
�hw,��X�����2�������|0y�m���U|U��4�{�@w�� �w�d�7#����-�����{��`Q����f&��t7�������!��G3mir:�6��s����3v��i�f�o�ɧ9�n��z�F�׋��z�=,�o�����LSu���쑤�ڻ$��[j���7�k��R<C�}���x,��L�,�#ym���WD�����~5�2]�UZ.�S��(筓�D�ғ�#��iA�]&c|in4i��&����D]�6$�K�>7۳�8�/�.��s��2�=�-�,T��6I�HNs��|{��J��Hێ�%��V<ך*Slϥ;3����qӻ�2Ϡ{��.H]�;����R��(1��bNy!:�i�aq.���-t��]�5,i���|�]jRf*O�^X��2;y�J3��d绉�^��y7��G��A���w;��{%���0�stcz?�s	��Z�X���
k�aC�kk�"��J �'9N��J��fS��KOiv�ݨ��g$�t��n�R��ԝM�ҙaSB�xg$]��I��������a��I'^��a�9��̯ҵ��b����?�FA{[׮l	���Ȝ�؉�����S�X��Ƹ��dn�VV<fY
I5)$I�)��R��%�m	�1�����j��]��dy�|{{:�Js���n���W�lk�dk�V'[Z5����^�]���{=�m�;��s+轠?:횫2~�����k�����7�!t���j���sGc?יN�ԻF�tw�$u�9G]�<٥��=�B���!�=2�ؐ%�B}|�!�%�.��T�ޕT��J��K��T>`HwS�ӻ��{�3�:�4�:[�@���bX�r�@��A�7�����@��� �U���� ���_��7�nL��?�I;|�#g3vݗ��u7�o����b�O'����U[3��w/��7wD�6skmF돧�ŢA�Isk���w�����Ҧ��V��Ldr��؇<�'��y�<�<�g���j�j�<7O�3�<cT��"ϊ�<u�y������̯V��|v1h�J�o'�l����km���Sg���6q�쬃މ���wd8G���Ry{�[�g��%�v��8��>C�	�ΐ��*���R�ɂ� x;����۠ɭ5�v��(x��X���d��-�0��N���C0htkMbp�x%��"�r�xV��u�J1f�l�_N�a������g�x�Jy̥�ωx�N)���D���N�����0��M����N����yEW]8(�?!/:6}����5�w�{��W�"R)/}K�(���8��_������X��_Lڏ�@F��ȼT��h>�םo����[4I���?�s��-|��F[K4?���|,k�7
�_�~�89Vʥo?�����'h�'ߧ+��� 혁�
ژ�m�@�ڈ�F�zh���do�ɕ��uX-�D�O9Z��e��ֿ��2*�0{v[<��Ut�^��r�^yW�Z�/�}ں�*]�VE��W�`�b�}�����ݥ�g����1�y��nvLyO�2���{���?1��$}��-�����=�q�?�f�>3�7�Ъ"�(�G�v��eʺt��?�z�iZR*W��ퟫ�a�Bn��ufzoH'ן���}�$�/����Y/ ��o���m�So��A���L}��Z��<���'{A+ֿ�ځ�g���sB�y���@+�<�F{~�@s��Ĕ�֩�QP[�,]_�y5��WM�R{���1���$֒��N��F��e�%����+�%o������]?;�;z����+W�Us;�����,�6��%��}�n.s�%�;|�2���u��2ͧ��u��Խ
�w�9�:�I��3Ko����a�C�9H�JW�_�һ�M�.,��s#껣/�M�+`�V��ۍ�a:wdp�@>�~������tU�k��;W������W�>�p�����H������L�f��Z�S��#��(����y�)���c�����앺�u�N�J{���F�F�����|��gZ��&�
� z�N��[��d|GP�J�{��s�:�Ɏ��}(/�wٷ�x>WN7cS���+�����5x�s��*������A�GY�;��?�hX�Wc�&]JU�蕲ٜ����$��ҌXq��z��Z̢߃��:����]��{�罐�˧��S��!͇��h~�:���N�ya���6��B�虜G�����bo*����ǝ��۝�R���\u���1��T��?��v�
��P�?�YA�<�~���9-}�|�~��H(��LuV����.�O��+{[����ޓ��ce/�g��q��5��+(���AѺZ�Q�7�F$g�d�ge?��O[ٯ�%���E�����������~��bݕ$�4Su�-�dY?4Y߱�?���Y�����X�w�Y����$���?�VP�,VP�u����3�L�GM�od1n�>��>/�<|
{�l�0�=b�~/���,�$���b}3���Z�e�|���,�˙֧@ϴ��X&��Ȳ�3����c�̣���5~�2 ���Ƃ@S� 	�d��!q� �b�Ʃ-"�bW��)m�	"/(Ҋ�1h;�-�8Gmqj�Ql������s��o�Z�j-����k�}ϸ�>��*;�����n�d|����y'�fηM7k��'��djG_��M��=�{�Y�	����s8����k�ěd�AЊ��K�,o�|��g��!O��Q#x�מ��H3�ß�<�i63��3��B}(^����]OBv}f�6��$����{���wg������h�����x��Te��`?m�q���$��N�1��~gs�M�
\�O�$���7K��t���l����w^�|3�^����������eǌ'�Γ��LXr�?)��n�~J�tI�J�sz�?f\�,j���������QX5_a��
��9��k��״MSz�Vו������~x�t�{ �����\G�ʯt���(��=Ղ�/�h���|�ǻ+�꠰�<׵������n���P��
c\W߯����+PD.�Ya��������k�*>��r�N��:`|�;��7�`�a0F�XV
��>��=z��}0x�n_Ȱ�֤h_���j�у}A�Į8���;��>������Ϭ?_�a�P�������-�aþh��I���R�O�/������®Xeط��y��'��K�>�?���ǂ�W�]�`�.�>����p^j�O�������*�f-׷Q����ž�?�<�l�i�G�?�|;)�q��A9�p��+�Vz����˼��LQIf��-W�I���s�+?���.wr�%ư��둇ϋ�W�yʭ�����b}�s���.�j��î�#o#~^#��G�����|W���:d\G�.����\�J>���������M
�����Pz|ͽ�G����pK%��n����V��د�ߦy����
���B��#`����S5~8����402�������yڼ����v�Ÿ.2�G�'rݢa�Q ��J��ʓs��U=IΙ�7K�i/�|f93��ǟ.��_�_��
�dė�PΟ�0���K���~Ҫ����<�йC�#g�����t�Y�n��
�����Iݟ������]$���k���Y]������u ���i���.����p+X
s��,��9��\
V�{�}`�9����,��9��\
���O���e?�_�<��T�lv ;����`18<,����Qp%��|||7z�P��g�w������
�y�q�d�U�_h���/5��3��������|�L���_ ���o����w��i�_�o4��M���O��b�Q�m�2sm��y@�?ǀ��M����|�ܫ�&r�*�=��n"�>��
�ΰ������8�A�=��،�K����}�*^ޣr�Q������	��q�N��f�>���0O����b�6���7�K<\��Z�o�#q�E�o����
�Q
.��ʳ_����,{�lC^��R?�{����1o��Z�'��k����Y?m���'\����B��mس~�|{�T��ً���z����O�l%�{�{�ȶ˟����0��1?G�/q���׺�_�~������%=����܈���R����m�d�>�\_=��o܊�5􌮗o����n��z����G�vn��E��\��.�C.�vޭ���������o����R���矟������O��7����R�ʬ��֊7�9�uROc��o�Cc��O��?��O���U��hn�wNQ��.�S�r�9����?ի�չ���&����D�F?4����s����'�ݹ��]�~��#묷��%k����=�����D�o��}E}\�w��+���;%�:U��;,�ߝ��g�ogQn�7$��|(G+�����</yS'��_�ʡ���<.�^o�@�a�;)�g;�7��P;e�߰�b�#�F����<6��G_���~��?7��R9���&�@�J��vR.�{�G��/��������U��)^~��~�X��_���FO�FE܅|v^�>�;5�|X�G;��h�ax�J��������
ٿ��跳��+����k���Su��1x���t�}{���h�9� ��SH�.��?`��:$ۨ�n���^FOŏ��
^�_�����X�g6��'�y�
/yvb�+�z�g��/y�"�����o�?��ޢ�*��������FO��?�u���c�������~����~���\^�<�N��
	���@�7�`?n��#$~�����f#�����#��<d$��^�[�'���y�J=k����V�&����q�,}\����ȥ��Ϗn�����k��y:��x��n�<5��^A9���������Y�}�A#���>����+�u�����o��8�����뮆���H����st�_=��I���Г;
��J}�(�����s���V��b=�m|�s�YgG��Q���������v��5�
��Ε�=μ`��o��z�m��ـΓsm� �G�N�9j�>���ƨy>n���wb�WY/�����.�C����=�����4�g��K?ߡ�Ö�;O���%�!c>Y3�}(��(�?���_�c�v���+���U�UE{�=�J�W�um|��k����i�oy��E��X�
��G��q�C����q��J������/z�����E���S�;2��3g<�k�˱�v=w�W��5����w����A�����c�V*<�1��x�	����x\�|h�7[�}?�=�F���T�F�� �>"g�}�2��b�/��K�� ��Si��ۑ�����wM��>�O)�cW����C�E�Kz��}Ov��sᗡ�7K���;����C�!���o?��*ι���'��^T�o/:��|���J��9���{�Ğ7��9R�MO��/8Y�����.�8�a�^?�����7��za���Ld�r����]�|e
��������.d���9�	Ե��s&�0��������L$����.���d��]�}n����#�C`
�<��iNg�{^���~c|��b��Q��k��T��mzܸ ^�#"����xNd*�wc=�~��+�=��閩��;�s�.�G[�}�D��Y� ��i���yyo�G����q����S�v�n |�݊�I�����~Υ��>�,��y��`)y;F����;�u�@�=^Զy#n9���g`E��������(��9a:������v������#�
=~���j\��M�1ڱ��?ܟ}J��n�<�*��8� �W�����_T��I�UROge��g��=#�53[��R#O�}���s
�ţ�zQ��)�s�S\��~c>҂�,��=O��|h�{��E��L;�o&���Oq��?�����=N�2\^�W�|p�"�$���	8�Y��O��/|�J��z}�K�2�c�v�����&��b$��r�bE�l���lW�ez�����ؽs��t�z�/g����k�n[���"� $"YJ�#E�%! ""A� !+DQbV$,Y<�`�@&H����Ou��Sս�Q{N�s�?�}��*������������yV����R~u��<o�I>��>������o?��H�#�a�Տ�q����}eO���/�yB�9Ľ�|���e�Uƍ��}����u�?�A�����e��|�<*֭��#���~�;ϣ�,��{�c��d��y�{Or����[k���i;�������
�_*�ol����q���Ǐ������|�8~����y���	��G��O�.��q1?<�[�oS3N�o$��_����]}��������by���F�_�@��T��������p�Z���q�|)��%��#��gh��M�_%{���[����~�Ť�O�����B�w$�`"��&�>df���R��c5�|�f�k�ϧ�yS���C�s�}A�-~��[8��%nX3��|�R��gګ���}�>��}^A�oWm�o�W���.��m���5�֯��O��}������5�+�~�5������8����S<W)�u}��g|�
6����-r"���%|{�������o��ݒ��)�'K���<�pp�rX��Sy�c8��#('������O+��������B��{�����n����u�~}���X���+�Eo������_�=Un���Ʋ��k�S/�K�m齧O{�G+�����8�5�������������`��]�9���9�ؿ��>�K����
~7����E�c������_�q��V�
��?�.��T�'| ��¿{�q�<���K���s8ο+���_���V �G}8D{��l���.��w��mb>�}b��8�.X��~����~[���7�/��ON��=�K)�z񞼏��p�����vO���=����=�˔�{$�z_Y>#��R�t���R>6�x�%���G��oDr:��}�~���_������K�1������E����l�������o���W���~q&�>@�������^
,[���[smv�����$��I��Ⱦ|�%(-,��	=0lsř���}��֝��\c�&�^��.�-0z]bP6��9������vHYG97J"�p"Mwj�uFQؿ�tǟчL��S������)�u;�&�3	�����e����X�=�}M��M�7<�&��rLu��8�
���֣�$�hs���G�8X���S�����g�FUb��"/�.��$[[����J�����׏��s`��9�����ܴ��׷�]2Ote '��-	2���
�g��sbs�� :��-ױ(��:۝vT����+�FG3|��ԭ����p��������A�'��`l�������Aİ���� �|��
H~ �/@<��J�m��Q�B%FQ�����ɰ?0 x�!a@)J�d&$�EmO���4;���DbG�n�y���󓏒9� ��=�đ4������pd��0%N�p2:�j�~�k�6�{�C�6�t�?$ ϲٌ⹋����e�"�ð�����xF�׫���U�T&Xg�dNC��w����1D��:�i�9���@�K�ЅI7�^��ޠf�>u3��܀eW����
�c���!4�!����a)Ӳ�@�@�M����y�/LZ�M�����F��]�;y��ў���v�[d��GۇÝI�ā8��_�ͽ���j���Fweɑ)1�׮=y0��Cԍ�F�5Ml�]�=8�ox8t����X��J{�����Icа�JB�����QvO;
z�̝�0M4�Bbq��幮���C�C����Ƞ�b%�G�(3�����i�N��������a�v�h�<>�og?��m'v`9\	8�����e��7��f7$
���Ў���
��S�|B,�̚6�bvm��X:Lȍɍt�%1��;��l�R��������&�d���%�df���ܱ���������-A0|<"S�D��w�ɠ���Dq�3])d^R]fC��էMɩ4�2`һ�k��Mj��J'2β4�Z�*'Ʉ͢bU��K��l'�z�q.'��L�o���U��Twn�L;2�,��Z���E��
�ٽB�彌G5vG]/i'�?e������s�Rfѳc��%w�^Rچ7I�k�$��R��K��Br�4��6�eQ�
�S6JW���3PV�vN]���}}H��NM�#�~hL]�W�'2��U�!q�v3
��3�R�=D����=H��酕��4Q2�=Y��a*&�:19�g��!(m²@����|}���n0Llo�y�Q�`e�b��m��KZh�@�62=�"�Qҵ}˕���%��2��6�7��rҰ�hU�#�
�*�4w1�#��\ޱ*Y!�K���z%PK���lO)Re�&
�Q�J*P䐺,�d�6 ����,�ԩ����q����*vX��iK�q�j(��\��U~�9��S�����J�c+�=#D�ѐ�bͥh�5��p��H#F��]+9
׬v5tWКo}��(\�b&l}�0�:9��x�6�tg�P4	��Ƀ�0{;F+��pڭK3Џ�PR���\��"��
@�ӟP�RW��+��;��j�ZF�;.ڽ�ݘM�G����|�1�Zۂ�4�y�_n$��vU�L�d<^�%���^�au+�s�R?��R+��,�*8�j���%�bke/6Y�F����ŉ��7�l��w,�ǐ��ΛP.�N�BT`���B�-:�ޛ����Vf�x�#1,,_��[ˠu}G��P���ׯxm����N�:TJ>J;K"��Q�%��~J�!�F�+��Xͱ"�
 ��r�g^}�m����5��e�U����+|��j�bKőe�27n���+�[��G�_��t�Tld�ii�|�M�B����ڻ�G�2ޞ�,YH�FH�
�E@�^.	�\�"mh��`H!R���H��|mK�+�Y0V5���qz�͒�M����+"�%���a�i�i͂��0ZD���}�R�@ރe�!�*��W�SZ۠V��~��4e�m��4�����`X�"���m)Hq��%��HT��T�<���{��QK�@�fwXq/�TQ4�.�x��w	!�UO�c���rw'\�Z�ʵ�0R�ٙ�U�)c��v��L��=Z���:�������raO���XѨݕ�*�h�͞]W��M꩒�B,�\ ���(��k%a>��h���Q�&��������>�O�H�1]��a��r�B��b��g@oy�5�h�.?�+Z�fA�:;����~�EK�L��j��R���ā��1�C�mQ�`��
H6-� w�;��"��E1�9� [8���pg;+�����՚
ү���W��Au6_
�-1����q_e���������I�Ţ��~ы���GA�;�D��5�ڥ�i�}Z���/Zƿ���*����o���o���o���o���o���o���o���o����g��  Ĺ  