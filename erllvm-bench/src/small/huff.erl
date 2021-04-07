%%
%% By Christer Jonsson
%%
%% History:
%%          2000-06-14 EJ   File IO Moved outside timing
%%

-module(huff).
-export([main/0,compile/1]).

main() ->
    garbage_collect(),
    statistics(runtime),
    Data = get_data(),
    {_,_LoadTime} = statistics(runtime),
    _OrgLength = length(Data),

    R = [], %loop(60,Data,0),
    length(R).

loop(0,_Data,R) -> R;
loop(N,Data,_R) -> loop(N-1,Data,pack_unpack(Data)).

compile(Flags) ->
    hipe:c(?MODULE,Flags).

% get_data(FileName) ->
%   {ok, _Dev, Fullname} =
%     file:path_open(code:get_path(), FileName, [read]),
%   {ok, Binary} = file:read_file(Fullname),
%   binary_to_list(Binary).

pack_unpack(Data) ->
   OrgSize = length(Data),
   FT = build_freq_trees(Data),
   Trees = sort_trees(FT, []),
   CodeTree = build_code_tree(Trees),
   Codes = make_codes(CodeTree, []),
   Bits = pack_data(Codes, Data),
   Bytes = bits_to_bytes(Bits),
   unpack(OrgSize, CodeTree, bytes_to_bits(Bytes)).


unpack(0,_CodeTree,_Bits) ->
   [];
unpack(Size, CodeTree, Bits) ->
   {Byte, RestBits} = find_byte(CodeTree, Bits),
   [Byte | unpack(Size-1, CodeTree, RestBits)].


find_byte({_, leaf, Byte}, Bits) ->
   {Byte, Bits};
find_byte({_, L,_R}, [1|Bits]) ->
   find_byte(L, Bits);
find_byte({_,_L, R}, [0|Bits]) ->
   find_byte(R, Bits).


bytes_to_bits([]) ->
    [];
bytes_to_bits([Byte|Bytes]) ->
    B7 = Byte div 128,
    B6 = (Byte-128*B7) div 64,
    B5 = (Byte-128*B7-64*B6) div 32,
    B4 = (Byte-128*B7-64*B6-32*B5) div 16,
    B3 = (Byte-128*B7-64*B6-32*B5-16*B4) div 8,
    B2 = (Byte-128*B7-64*B6-32*B5-16*B4-8*B3) div 4,
    B1 = (Byte-128*B7-64*B6-32*B5-16*B4-8*B3-4*B2) div 2,
    B0 = (Byte-128*B7-64*B6-32*B5-16*B4-8*B3-4*B2-2*B1),
    [B7,B6,B5,B4,B3,B2,B1,B0 | bytes_to_bits(Bytes)].


bits_to_bytes([B7, B6, B5, B4, B3, B2, B1, B0 | Rest]) ->
    [(B7*128+B6*64+B5*32+B4*16+B3*8+B2*4+B1*2+B0) | bits_to_bytes(Rest)];
bits_to_bytes([B7, B6, B5, B4, B3, B2, B1]) ->
    [B7*128+B6*64+B5*32+B4*16+B3*8+B2*4+B1*2];
bits_to_bytes([B7, B6, B5, B4, B3, B2]) ->
    [B7*128+B6*64+B5*32+B4*16+B3*8+B2*4];
bits_to_bytes([B7, B6, B5, B4, B3]) ->
    [B7*128+B6*64+B5*32+B4*16+B3*8];
bits_to_bytes([B7, B6, B5, B4]) ->
    [B7*128+B6*64+B5*32+B4*16];
bits_to_bytes([B7, B6, B5]) ->
    [B7*128+B6*64+B5*32];
bits_to_bytes([B7, B6]) ->
    [B7*128+B6*64];
bits_to_bytes([B7]) ->
    [B7*128];
bits_to_bytes([]) ->
    [].


pack_data(_Codes, []) ->
   [];
pack_data(Codes, [Byte|Rest]) ->
   append(get_code(Byte, Codes),pack_data(Codes, Rest)).


get_code(Index, [{I, Bits}|_]) when Index =:= I ->
   Bits;
get_code(Index, [_|Rest]) ->
   get_code(Index, Rest);
get_code(_Index, []) ->
    io:format("error\n",[]),
    exit(error).


make_codes(Tree, Bits) ->
   make_codes(Tree,Bits,[]).

make_codes({_, leaf, Byte}, Bits, Acc) ->
    [{Byte, reverse(Bits)}|Acc];
make_codes({_, R, L}, Bits,Acc) ->
    make_codes(R, [1|Bits], make_codes(L, [0|Bits], Acc)).

%%
%% Make one huffman tree out of a list of trees.
%%

build_code_tree([Tree]) ->
   Tree;
build_code_tree([{Val1, R1, L1}, {Val2, R2, L2} | Rest]) ->
   build_code_tree(insert_tree({Val1+Val2, {Val1, R1, L1}, {Val2, R2, L2}},
			       Rest)).

%%
%% Sort a list of leaves so that those with least frequence is first.
%% Nodes with frequence 0 are removed.
%%

sort_trees([], Sorted) ->
   Sorted;
sort_trees([T|Trees], Sorted) ->
   sort_trees(Trees, insert_tree(T, Sorted)).


%%
%% Insert a tree in a sorted list (least frequencey first)
%%

insert_tree({0, _, _}, []) ->
   [];
insert_tree(Tree, []) ->
   [Tree];
insert_tree({0, _, _}, Trees)  ->
   Trees;
insert_tree({Val1, R1, L1}, [{Val2, R2, L2}|Rest]) when Val1 < Val2 ->
   [{Val1, R1, L1}, {Val2, R2, L2}|Rest];
insert_tree(T1, [T2|Rest]) ->
   [T2|insert_tree(T1, Rest)].


%%
%% Makes a list of 256 leaves each containing the frequency of a bytecode.
%%

build_freq_trees(Data) ->
   build_freq_table(Data, 0).

build_freq_table(_, 256) ->
   [];
build_freq_table(Data, X) ->
   [{occurs(X, Data, 0), leaf, X} | build_freq_table(Data, X+1)].


occurs(_, [], Ack) ->
   Ack;
occurs(X, [Y|Rest], Ack) when X == Y ->
   occurs(X, Rest, Ack+1);
occurs(X, [_|Rest],Ack) ->
   occurs(X, Rest, Ack).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%5
%%
%% Some utilities
%%

reverse(X) ->
   reverse(X, []).
reverse([H|T], Y) ->
   reverse(T, [H|Y]);
reverse([], X) ->
   X.

append([H|T], Z) ->
   [H|append(T, Z)];
append([], X) ->
   X.


get_data() ->
   "
Documentation for UUENCODE/DECODE 5.15

UU-encoding is a way to code a file which may contain any characters into a
standard character set that can be reliably sent over diverse networks.


THE CHARACTER ENCODING:

The basic scheme is to break groups of 3 eight bit characters (24 bits) into 4
six bit characters and then add 32 (a space) to each six bit character which
maps it into the readily transmittable character.  Another way of phrasing this
is to say that the encoded 6 bit characters are mapped into the set:
        `!\"#$%&'()*+,-./012356789:;<=>?@ABC...XYZ[\\]^_
for transmission over communications lines.

As some transmission mechanisms compress or remove spaces, spaces are changed
into back-quote characters (a 96).  (A better scheme might be to use a bias of
33 so the space is not created, but this is not done.)

Another newer less popular encoding method, called XX-encoding uses the set:
        +-01..89ABC...XYZabc...xyz

In my opinion, XX-encoding is superior to UU-encoding because it uses more
\"normal\" characters that are less likely to get corrupted.  In fact several of
the special characters in the UU set do not get thru an EBCDIC to ASCII
translation correctly.  Conversely, an advantage of the UU set is that it does
not use lower case characters.  Now-a-days both upper and lower case are sent
with no problems; maybe in the communications dark ages, there was a problem
with lower case.

This \"UU\" encode/decode pair can handle either XX or UU encoding.  The encode
program defaults to creating a UU encoded file; but can be run with a \"-x\"
option to create an XX encoding.

The decode program defaults to autodetect.  However the program can get confused
by comment lines preceeding the actual encoded data.  The decode mode can be
forced to UU or XX with the \"-u\" or \"-x\" parameter.

Another option is for the character mapping table to be inserted at the front of
the file.  The format for this is discussed later.  The table parameters are
detected and used by this decode program.  (A table will override the \"-x\" or
\"-u\" parameters.) The encode program can be run with a \"-t\" option which tells
it to put the table into the encoded file.

A third encode mapping is the one used by Brad Templeton's ABE program.  This is
not handled by these programs as the check and control information surrounding
the actual encoded data is in a different form.

From a theoritical view, this encoding is breaking down 24 bits modulo 64.  Note
that 64**3 is = 2**24.  The result is 24 bits in for 32 bits out, a 33% size
increase.  Note that 85**5 > 2**32.  Also note that there are 94 transmittable
ASCII characters (from 0x21 thru 0x7e).  Thus modulo 85 encoding (the atob
encoder) transforms 32 bits to 5 ASCII chars or 40 bits for a 25% size increase.

The trade off in the module 85 encoding is that many communications systems do
not reliably transmit 85 ASCII characters.  The tilda, carat, brackets, and
sometimes upper or lower case frequently get corrupted.

COMPOSING A LINE OF ENCODED CHARACTERS:

A small number of eight bit characters are encoded into a single line and a
count is put at the start of the line.  (Most lines in an encoded file have 45
encoded characters.  When you look at a UU-encoded file note that most lines
start with the letter \"M\".  \"M\" is decimal 77 which, minus the 32 bias, is 45.)

This encode program puts a check character at the end of each line.  The check
is the sum of all the encoded characters, before adding the mapping, modulo 64.

Note: Horton 9/1/87 UUENCODE has a bug in the line check algorithm; it uses the
sum of the original, not the encoded characters.  This decode program accepts
either form of line check character.

In previous versions (4.13 and lower) the line check characters was generated by
default by this encode program and was supressed with the \"-L\" option.  One
reason to supress them is if they will be decoded by one of the old Horton
decoders.  Most decoders either accept this form of check or simply stop looking
after the line length is exhausted.  My feelings are mixed about the line
checksums because errors of this type essentially never occur.

However with modern, error-free communications systems and with the CRC checks
on the entire file (see below) I have made the default for uuencoding to have NO
line level check characters effective version 4.21.  The \"-L\" option on uuencode
turns on generation of line checksums.  If you have a really bad communications
system and you want to isolate a problem, turn them on.

Uudecode automatically checks for the presense line checksums, so the default
for uudecode is to leave line level checks on; if there are some problems the
\"-L\" option for uudecode turns them off.  Sometimes there is junk at the end of
the line which causes spurious line checksum errors.

I have encountered various other ways that encoders end lines.  One encoder put
a \"M\" at both the start and end of the line.  Another used a line count
character.  This decode program checks all of these.  I would not be surprised
if some encoder out there ends lines with astrological symbols.  If you
encounter some other wierd form of encoded file, let me know.


PACKAGING THE LINES INTO FILES:

The lines of encoded data can be preceded by comments and by network addressing
information.  The encoded data is directly preceded by a line containing:

             begin <file-mode> <file-name>

This line is created by the encoding program.  The decode program scans the file
looking for \"begin\" in column 1.

The final end of encoded data is an encoded line with zero encoded characters (a
back-quote), followed by a line containing \"end\".

For integrity checking, various encode programs insert checksums for the entire
file.  This decode tries to check for all known types of file checksums.  This
is discussed in more detail later.

This encode program puts a header line, containing the section number and file
name, in front of every section:

         \"section <number> of uuencode of file <file name>\"

At the end of a section the encode program inserts a line containing checksum
and file size information.  This can be suppressed with the \"-c\" option.

The transmissions on comp.binaries.ibm.pc contain two different types of section
number/file-name lines.  The first is the \"Archive-name line\"; the other is the
\"part line\".

The format of the Archive-name line is:
        \"Archive-name: <name>/part<number>\"
for example:
        Archive-name: diskutl/part02

The format of the part line is:
        <name> part<number>/<max-number>
for example:
        diskutl part02/03

This program checks for consistency of these names and numbers as of release
5.0.

All the \"integrity fields\" (the checksum, the line check, and the section header
line) are inserted in a way that they will be ignored by other UUDECODE programs
that cannot handle them.  This decode program does not require any of these
fields; if not present, integrity checking is not done.  This program pair is
100% downward compatible!


FILE NAMES:

The default name of the file to encode into is the base name of the file you are
encoding plus the \".UUE\" extension for UU encoding.

        uuencode foo.bar                produces file foo.uue.

If the -X (upper case) option is used, then the file will be XXencoded (see
above); and will be saved with the default \".XXE\" extension.

Uuencode can also be called with a second parameter which is the specific file
name of the encoded file.  If this file name has no extension, the above default
(.UUE or .XXE is used).

        uuencode    foo  foo.bar        encode foo to foo.bar
        uuencode -X foo  xxfoo          encode foo to foo.xxe
        uuencode -X foo  xxfoo.bar      encode foo to xxfoo.bar
        uuencode    foo  xxfoo.         encode foo to xxfoo.

Uudecode defaults to look for files with the \".UUE\" and the \".XXE\" extension.
This only applies if uudecode is called without a file name extension:

        uudecode    foo         look for file foo.uue, then foo.xxe
        uudecode -u foo         look for file foo.uue only
        uudecode -x foo         look for file foo.xxe, then foo.uue

If uudecode is called with a file name extension, then that is used:

        uudecode foo.XXX        decode file foo.xxx
        uudecode foo.           decode file foo  with no extension


SPLITING UP LONG FILES:

Long files are broken into several sections before transmission.  This is done
because very large files are cumbersome to handle and because some networks
require files to be less than 64K bytes.

This encode program automatically breaks large encoded files into sections.
This split is controlled by several options.  First the \"-s\" option tells encode
not to split the file.  The \"-s nnn\" option tells encode to split the file into
hunks of \"nnn\" lines.  The default is 950 lines which is about 59k.  Sometimes
extensive comments are put into the first file; thus it may be necessary for the
first file to contain fewer encoded lines.  The \"-h nnn\" option tells encode to
leave room for \"nnn\" additional lines in the first file.

If the data file being encoded is called FOO.ZIP, then the encode program names
the encoded files FOO1.UUE, FOO2.UUE, etc.  (Or .XXE if the -X option is used.)

The decode program searches for the various sections, scans over preliminary
comments and decodes all as if they were one big file.  Decode is passed the
base file name \"FOO\".

Decode can (but rarely does) get confused and thinks header lines are encoded
data.  If so, edit the file and try again.  This has only happened once to me
and I have decoded a lot of files.

When decode encounters a premature end-of-file or some data which is not
decodable, it assumes the end of a file section.  Decode is conservative when it
encounters data it cannot decode (better an error than a bad file).

Usually this undecodable data is valid \"trailer\" data put at the end of file for
data transmission purposes.  However the file may be bad.  So decode continues
to scan the file, if decode then encounters a line which is decodable it assumes
the file is bad.  Or if there are more than 30 lines remaining in the file,
decode assumes the file is bad.

When decode encounters a valid end of file section it must get the next file in
sequence.  If the file name ends with a number, decode tries the next file name
in numeric sequence.  Otherwise decode asks for a file name.  If this file does
not contain decodable data, decode asks for another file to try.

If multiple sections are saved in a single file, the sections must have one of
the three (above) types of section header lines for validation.  Decode builds a
table of section information so it can go back and reread if sections are not
saved in order.

The \"SECTION\" line inserted by the UUENCODE program is used for validity
checking only.  If not present, decode will accept any file containing encoded
lines.


OTHER FILE FORMS:

Sometimes files are wrapped in shell archives that automatically check
sequencing and call uudecode for you on Unix systems.  If you prefer to download
the raw files to MS-DOS, uudecode 5.15 will filter simple shell scripts, that
use the Unix 'sed' command, and decode the data automatically.

There is one more rarely used feature of ENCODE: many input files can be encoded
into one large encode file.  (I have never seen this used.) The end of an input
file is a zero length encoded line, followed by another \"begin\" line instead of
by an \"end\" line.  This decode program will decode this sort of file; but the
encode will only handle a single input file.


FILE LEVEL CHECKSUMS:

There are three types of file checksums found in encoded files:

       UUENCODE 2.14 and below inserted lines that gave the section
       size and the original input file size.  This is supplanted
       by a better technique in 3.07; but 3.07 UUDECODE still checks
       and validates the old form

       UUENCODE 3.07 and Rahul Dhesi''s encode scripts compute a Unix
       \"sum -r\" on the encoded sections and on the original input file.
       A difference is that UUENCODE 3.07 puts the expected \"sum -r\"
       and size at the end of a file while Rahul''s scripts put them at
       begining.  This UUDECODE analyzes either.

       The third form of checksum is a full 32 bit CRC that Rahul's script
       inserts.  My code does not handle this.  Rahul has written the
       BRIK program to check them.  If there is a \"sum -r\" failure, BRIK
       analysis should be considered.

Unisys Unix platforms put a line containing just the original file size at the
end of the encoded file.  My code checks this.


TABLE LINES:

Some encoded files but the mapping used at the front of the encoded file, just
in front of the \"begin\" line.  The format for this is:

                   table
                   first 32 characters
                   second 32 characters

All this starts in column 1.

If decode encounters a table specification, it uses it and overrides any command
line parameters.  Encode will create the table lines if run with the \"-t\"
parameter.


COMPLETION CODES:

On successful completion, UUDECODE sets ERRORLEVEL to 0.  If there are any
problems, ERRORLEVEL is set to non-zero.

Most of the options to UUDECODE are obvious.  However, the \"-e\" option needs
more explanation.  The purpose of \"-e\" is to automatically run an un-archiver
(like ZOO or PKUNPAK) when UUDECODE successfully completes.  If the \"-e\" option
is given, UUDECODE calls BAT file UNARCUUE on successful completion UNARCUUE is
passed two parameters:

                the filename decoded (with no extension)
                the file extension.

Normally the file extension tells which un-archiver to call.  The UNARCUUE BAT
file, can test these parameters and call the necessary un-archiver.


This works well for me.  On UNIX I find a program I want in three sections:
              PRG1, PRG2, PRG3.
I copy the three files down to my PC as PRG1.UUE, PRG2.UUE, and PRG3.UUE.  I
then just enter UUDECODE PRG and the thing decodes.


If the -X (upper case) option is used, then the file will be XXencoded (see
above); and will be saved with the default \".XXE\" extension.

Uuencode can also be called with a second parameter which is the specific file
name of the encoded file.  If this file name has no extension, the above default
(.UUE or .XXE is used).

        uuencode    foo  foo.bar        encode foo to foo.bar
        uuencode -X foo  xxfoo          encode foo to foo.xxe
        uuencode -X foo  xxfoo.bar      encode foo to xxfoo.bar
        uuencode    foo  xxfoo.         encode foo to xxfoo.

Uudecode defaults to look for files with the \".UUE\" and the \".XXE\" extension.
This only applies if uudecode is called without a file name extension:

        uudecode    foo         look for file foo.uue, then foo.xxe
        uudecode -u foo         look for file foo.uue only
        uudecode -x foo         look for file foo.xxe, then foo.uue

If uudecode is called with a file name extension, then that is used:

        uudecode foo.XXX        decode file foo.xxx
        uudecode foo.           decode file foo  with no extension


SPLITING UP LONG FILES:

Long files are broken into several sections before transmission.  This is done
because very large files are cumbersome to handle and because some networks
require files to be less than 64K bytes.

This encode program automatically breaks large encoded files into sections.
This split is controlled by several options.  First the \"-s\" option tells encode
not to split the file.  The \"-s nnn\" option tells encode to split the file into
hunks of \"nnn\" lines.  The default is 950 lines which is about 59k.  Sometimes
extensive comments are put into the first file; thus it may be necessary for the
first file to contain fewer encoded lines.  The \"-h nnn\" option tells encode to
leave room for \"nnn\" additional lines in the first file.

If the data file being encoded is called FOO.ZIP, then the encode program names
the encoded files FOO1.UUE, FOO2.UUE, etc.  (Or .XXE if the -X option is used.)

The decode program searches for the various sections, scans over preliminary
comments and decodes all as if they were one big file.  Decode is passed the
base file name \"FOO\".

Decode can (but rarely does) get confused and thinks header lines are encoded
data.  If so, edit the file and try again.  This has only happened once to me
and I have decoded a lot of files.

When decode encounters a premature end-of-file or some data which is not
decodable, it assumes the end of a file section.  Decode is conservative when it
encounters data it cannot decode (better an error than a bad file).

Usually this undecodable data is valid \"trailer\" data put at the end of file for
data transmission purposes.  However the file may be bad.  So decode continues
to scan the file, if decode then encounters a line which is decodable it assumes
the file is bad.  Or if there are more than 30 lines remaining in the file,
decode assumes the file is bad.

When decode encounters a valid end of file section it must get the next file in
sequence.  If the file name ends with a number, decode tries the next file name
in numeric sequence.  Otherwise decode asks for a file name.  If this file does
not contain decodable data, decode asks for another file to try.

If multiple sections are saved in a single file, the sections must have one of
the three (above) types of section header lines for validation.  Decode builds a
table of section information so it can go back and reread if sections are not
saved in order.

The \"SECTION\" line inserted by the UUENCODE program is used for validity
checking only.  If not present, decode will accept any file containing encoded
lines.


OTHER FILE FORMS:

Sometimes files are wrapped in shell archives that automatically check
sequencing and call uudecode for you on Unix systems.  If you prefer to download
the raw files to MS-DOS, uudecode 5.15 will filter simple shell scripts, that
use the Unix 'sed' command, and decode the data automatically.

There is one more rarely used feature of ENCODE: many input files can be encoded
into one large encode file.  (I have never seen this used.) The end of an input
file is a zero length encoded line, followed by another \"begin\" line instead of
by an \"end\" line.  This decode program will decode this sort of file; but the
encode will only handle a single input file.


FILE LEVEL CHECKSUMS:

There are three types of file checksums found in encoded files:

       UUENCODE 2.14 and below inserted lines that gave the section
       size and the original input file size.  This is supplanted
       by a better technique in 3.07; but 3.07 UUDECODE still checks
       and validates the old form

       UUENCODE 3.07 and Rahul Dhesi''s encode scripts compute a Unix
       \"sum -r\" on the encoded sections and on the original input file.
       A difference is that UUENCODE 3.07 puts the expected \"sum -r\"
       and size at the end of a file while Rahul''s scripts put them at
       begining.  This UUDECODE analyzes either.

       The third form of checksum is a full 32 bit CRC that Rahul's script
       inserts.  My code does not handle this.  Rahul has written the
       BRIK program to check them.  If there is a \"sum -r\" failure, BRIK
       analysis should be considered.

Unisys Unix platforms put a line containing just the original file size at the
end of the encoded file.  My code checks this.


TABLE LINES:

Some encoded files but the mapping used at the front of the encoded file, just
in front of the \"begin\" line.  The format for this is:

                   table
                   first 32 characters
                   second 32 characters

All this starts in column 1.

If decode encounters a table specification, it uses it and overrides any command
line parameters.  Encode will create the table lines if run with the \"-t\"
parameter.


COMPLETION CODES:

On successful completion, UUDECODE sets ERRORLEVEL to 0.  If there are any
problems, ERRORLEVEL is set to non-zero.

Most of the options to UUDECODE are obvious.  However, the \"-e\" option needs
more explanation.  The purpose of \"-e\" is to automatically run an un-archiver
(like ZOO or PKUNPAK) when UUDECODE successfully completes.  If the \"-e\" option
is given, UUDECODE calls BAT file UNARCUUE on successful completion UNARCUUE is
passed two parameters:

                the filename decoded (with no extension)
                the file extension.

Normally the file extension tells which un-archiver to call.  The UNARCUUE BAT
file, can test these parameters and call the necessary un-archiver.


This works well for me.  On UNIX I find a program I want in three sections:
              PRG1, PRG2, PRG3.
I copy the three files down to my PC as PRG1.UUE, PRG2.UUE, and PRG3.UUE.  I
then just enter UUDECODE PRG and the thing decodes.


Done privately and not for profit (freeware).  Suggestions appreciated.
The programs are written in Turbo Pascal 5.5 with about 5% TASM for speed.  The
source is not public domain.  I would entertain consulting contracts for porting
to other hardware platforms.  Also if included in your for profit product,
please contact me.


Richard Marks
931 Sulgrave Lane
Bryn Mawr, PA 19010

Copyright Richard E. Marks, Bryn Mawr, PA, 1992

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

Change log (started with 5.13):
5.15
5.15 fixes a problem with trailing blanks on lines.

5.14:

5.14 fixes a minor bug in which a redundant error message was produced
when decoding single section files.


5.13 VERSUS 5.10:

5.13 decode has a command line option that disables all interactive
responses to make it more useable from some BBS systems.  Examine the
\"y\" and \"Y\" options.

5.13 can increment the number on files up to five digits.  The prior
limit was two digits.  You can now save files with names based on news
article numbers.

5.13 can decode files encoded into 100 or more parts.  A restriction is
that if there are more than 100 parts, the sections MUST be in order.

#
Done privately and not for profit (freeware).  Suggestions appreciated.
The programs are written in Turbo Pascal 5.5 with about 5% TASM for speed.  The
source is not public domain.  I would entertain consulting contracts for porting
to other hardware platforms.  Also if included in your for profit product,
please contact me.


Richard Marks
931 Sulgrave Lane
Bryn Mawr, PA 19010

Copyright Richard E. Marks, Bryn Mawr, PA, 1992

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

Change log (started with 5.13):
5.15
5.15 fixes a problem with trailing blanks on lines.

5.14:

5.14 fixes a minor bug in which a redundant error message was produced
when decoding single section files.


5.13 VERSUS 5.10:

5.13 decode has a command line option that disables all interactive
responses to make it more useable from some BBS systems.  Examine the
\"y\" and \"Y\" options.

5.13 can increment the number on files up to five digits.  The prior
limit was two digits.  You can now save files with names based on news
article numbers.

5.13 can decode files encoded into 100 or more parts.  A restriction is
that if there are more than 100 parts, the sections MUST be in order.

#If the -X (upper case) option is used, then the file will be XXencoded (see
above); and will be saved with the default \".XXE\" extension.

Uuencode can also be called with a second parameter which is the specific file
name of the encoded file.  If this file name has no extension, the above default
(.UUE or .XXE is used).

        uuencode    foo  foo.bar        encode foo to foo.bar
        uuencode -X foo  xxfoo          encode foo to foo.xxe
        uuencode -X foo  xxfoo.bar      encode foo to xxfoo.bar
        uuencode    foo  xxfoo.         encode foo to xxfoo.

Uudecode defaults to look for files with the \".UUE\" and the \".XXE\" extension.
This only applies if uudecode is called without a file name extension:

        uudecode    foo         look for file foo.uue, then foo.xxe
        uudecode -u foo         look for file foo.uue only
        uudecode -x foo         look for file foo.xxe, then foo.uue

If uudecode is called with a file name extension, then that is used:

        uudecode foo.XXX        decode file foo.xxx
        uudecode foo.           decode file foo  with no extension


SPLITING UP LONG FILES:

Long files are broken into several sections before transmission.  This is done
because very large files are cumbersome to handle and because some networks
require files to be less than 64K bytes.

This encode program automatically breaks large encoded files into sections.
This split is controlled by several options.  First the \"-s\" option tells encode
not to split the file.  The \"-s nnn\" option tells encode to split the file into
hunks of \"nnn\" lines.  The default is 950 lines which is about 59k.  Sometimes
extensive comments are put into the first file; thus it may be necessary for the
first file to contain fewer encoded lines.  The \"-h nnn\" option tells encode to
leave room for \"nnn\" additional lines in the first file.

If the data file being encoded is called FOO.ZIP, then the encode program names
the encoded files FOO1.UUE, FOO2.UUE, etc.  (Or .XXE if the -X option is used.)

The decode program searches for the various sections, scans over preliminary
comments and decodes all as if they were one big file.  Decode is passed the
base file name \"FOO\".

Decode can (but rarely does) get confused and thinks header lines are encoded
data.  If so, edit the file and try again.  This has only happened once to me
and I have decoded a lot of files.

When decode encounters a premature end-of-file or some data which is not
decodable, it assumes the end of a file section.  Decode is conservative when it
encounters data it cannot decode (better an error than a bad file).

Usually this undecodable data is valid \"trailer\" data put at the end of file for
data transmission purposes.  However the file may be bad.  So decode continues
to scan the file, if decode then encounters a line which is decodable it assumes
the file is bad.  Or if there are more than 30 lines remaining in the file,
decode assumes the file is bad.

When decode encounters a valid end of file section it must get the next file in
sequence.  If the file name ends with a number, decode tries the next file name
in numeric sequence.  Otherwise decode asks for a file name.  If this file does
not contain decodable data, decode asks for another file to try.

If multiple sections are saved in a single file, the sections must have one of
the three (above) types of section header lines for validation.  Decode builds a
table of section information so it can go back and reread if sections are not
saved in order.

The \"SECTION\" line inserted by the UUENCODE program is used for validity
checking only.  If not present, decode will accept any file containing encoded
lines.


OTHER FILE FORMS:

Sometimes files are wrapped in shell archives that automatically check
sequencing and call uudecode for you on Unix systems.  If you prefer to download
the raw files to MS-DOS, uudecode 5.15 will filter simple shell scripts, that
use the Unix 'sed' command, and decode the data automatically.

There is one more rarely used feature of ENCODE: many input files can be encoded
into one large encode file.  (I have never seen this used.) The end of an input
file is a zero length encoded line, followed by another \"begin\" line instead of
by an \"end\" line.  This decode program will decode this sort of file; but the
encode will only handle a single input file.


FILE LEVEL CHECKSUMS:

There are three types of file checksums found in encoded files:

       UUENCODE 2.14 and below inserted lines that gave the section
       size and the original input file size.  This is supplanted
       by a better technique in 3.07; but 3.07 UUDECODE still checks
       and validates the old form

       UUENCODE 3.07 and Rahul Dhesi''s encode scripts compute a Unix
       \"sum -r\" on the encoded sections and on the original input file.
       A difference is that UUENCODE 3.07 puts the expected \"sum -r\"
       and size at the end of a file while Rahul''s scripts put them at
       begining.  This UUDECODE analyzes either.

       The third form of checksum is a full 32 bit CRC that Rahul's script
       inserts.  My code does not handle this.  Rahul has written the
       BRIK program to check them.  If there is a \"sum -r\" failure, BRIK
       analysis should be considered.

Unisys Unix platforms put a line containing just the original file size at the
end of the encoded file.  My code checks this.


TABLE LINES:

Some encoded files but the mapping used at the front of the encoded file, just
in front of the \"begin\" line.  The format for this is:

                   table
                   first 32 characters
                   second 32 characters

All this starts in column 1.

If decode encounters a table specification, it uses it and overrides any command
line parameters.  Encode will create the table lines if run with the \"-t\"
parameter.


COMPLETION CODES:

On successful completion, UUDECODE sets ERRORLEVEL to 0.  If there are any
problems, ERRORLEVEL is set to non-zero.

Most of the options to UUDECODE are obvious.  However, the \"-e\" option needs
more explanation.  The purpose of \"-e\" is to automatically run an un-archiver
(like ZOO or PKUNPAK) when UUDECODE successfully completes.  If the \"-e\" option
is given, UUDECODE calls BAT file UNARCUUE on successful completion UNARCUUE is
passed two parameters:

                the filename decoded (with no extension)
                the file extension.

Normally the file extension tells which un-archiver to call.  The UNARCUUE BAT
file, can test these parameters and call the necessary un-archiver.


This works well for me.  On UNIX I find a program I want in three sections:
              PRG1, PRG2, PRG3.
I copy the three files down to my PC as PRG1.UUE, PRG2.UUE, and PRG3.UUE.  I
then just enter UUDECODE PRG and the thing decodes.


Done privately and not for profit (freeware).  Suggestions appreciated.
The programs are written in Turbo Pascal 5.5 with about 5% TASM for speed.  The
source is not public domain.  I would entertain consulting contracts for porting
to other hardware platforms.  Also if included in your for profit product,
please contact me.


Richard Marks
931 Sulgrave Lane
Bryn Mawr, PA 19010

Copyright Richard E. Marks, Bryn Mawr, PA, 1992

. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

Change log (started with 5.13):
5.15
5.15 fixes a problem with trailing blanks on lines.

5.14:

5.14 fixes a minor bug in which a redundant error message was produced
when decoding single section files.


5.13 VERSUS 5.10:

5.13 decode has a command line option that disables all interactive
responses to make it more useable from some BBS systems.  Examine the
\"y\" and \"Y\" options.

5.13 can increment the number on files up to five digits.  The prior
limit was two digits.  You can now save files with names based on news
article numbers.

5.13 can decode files encoded into 100 or more parts.  A restriction is
that if there are more than 100 parts, the sections MUST be in order.

".