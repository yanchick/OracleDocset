#!/opt/perl/bin/perl
##############################################################################
# File: analyzer_elastic_json.pl
# Copyright 2014, 2015, Oracle and/or its affiliates. All rights reserved.
# $Id: analyzer_elastic_json.pl,v 1.0 2015/04/29 12:02:51 vivkumar Exp $
##############################################################################

use File::Find;
use File::Spec;
use File::Compare;
use HTML::TokeParser;
use Carp;
use Time::Local;
use Getopt::Long;
use Pod::Usage;
use HTML::Entities;
use LWP::UserAgent;
use XML::LibXML;
use IO::File;
use Pod::Usage;
use utf8;
use warnings;
use List::MoreUtils qw( any );
use English qw( -no_match_vars );
use Readonly;
use Try::Tiny;
use Pod::Usage;
use Cwd 'abs_path';
require Encode;
use Encode;

our $VERSION = 2015.04029;
my $folder                  = q();
my $library_partnumber      = q();
my $context                 = q();
my %library_data            = ();
my %library_data_docid      = ();
my %additional_data         = ();
my $indexcounter            = 0;
my $libraryurl              = 0;
my @html_files_from_library = ();
my %folderpnmapping         = ();
my %all_encoding = ();
my %chunk_storage = ();
&get_encoding_list();

Readonly my $PARTNO => qr{ [[:alpha:]] \d{5} [-_] \d{1,2} }xms;

Readonly my $SHORTCUT_CHAR_LENGTH            => 3;
Readonly my $SHORTCUT_CHAR_LENGTH_FOUR       => 4;
Readonly my $SHORTCUT_CHAR_LENGTH_FIVE       => 5;
Readonly my $SHORTCUT_CHAR_LENGTH_SIX        => 6;
Readonly my $SHORTCUT_CHAR_LENGTH_SEVEN      => 7;
Readonly my $SHORTCUT_CHAR_LENGTH_EIGHT      => 8;
Readonly my $SHORTCUT_CHAR_LENGTH_NINE       => 9;
Readonly my $SHORTCUT_CHAR_LENGTH_TEN        => 10;
Readonly my $SHORTCUT_CHAR_LENGTH_SIXTY      => 60;
Readonly my $SHORTCUT_CHAR_LENGTH_FIFTY      => 50;
Readonly my $SHORTCUT_CHAR_LENGTH_TWOFIFTY   => 250;
Readonly my $SHORTCUT_CHAR_LENGTH_THIRTYFIVE => 35;
Readonly my $SHORTCUT_CHAR_LENGTH_NINENINE   => 99;
Readonly my $INITIAL                         => -1;
Readonly my $ADDER                           => 1900;
Readonly my $HUNDRED                         => 100;
Readonly my $ELEVEN                          => 11;
Readonly my $TWELVE                          => 12;
Readonly my $THIRTEEN                        => 13;
Readonly my $THREETWO                        => 32;
Readonly my $THREEEIGHT                      => 38;
Readonly my $THREEFOUR                       => 34;
Readonly my $THREENINE                       => 39;
Readonly my $SIXTWO                          => 62;
Readonly my $ONETWOSIX                       => 126;

my $server_elastic_search = q(stdoc.us.oracle.com);
my $pdb_url               = q(http://pdb.us.oracle.com/);
my %errors                = ();
my $whichpn               = "";
my $tableprocessing;
Getopt::Long::Configure('gnu_getopt');
GetOptions(
    'input|f=s' => \$folder,
    'lib|l=s'   => \$library_partnumber,
    'ctx|c=s'   => \$context,
    'url|u=s'   => \$libraryurl,
    'table|t=s' => \$tableprocessing
);

$whichpn = $library_partnumber;
%subfolder_mappings = ();
&getFolderMappings ($whichpn);

my @administrator_pns = ("e49548", "e49573", "e50708", "e51676", "e51667", "e51666", "e50710", 
                         "e37261", "e40026", "e49574", "e49554", "e49599", "e49564", "e49601", 
                         "e49611", "e49613", "e49880", "e49622", "e49571", "e51077", "e49577", 
                         "e49595", "e50784", "e50989", "e50987", "e50988", "e50994", "e50990", 
                         "e50992", "e50993", "e51078", "e51153", "e39993", "e39998", "e40008", 
                         "e40009");

my @developer_pns     = ("e51622", "e38763", "e41172", "e51153", "e50784", 
                         "e37261", "e50335", "e50269");

my @user_pns          = ("e49617", "e41248", "e41354", "e41353", "e41352", "e49888",
                         "e49573", "e49574", "e49599", "e49564", "e49601", "e49611",
                         "e49613", "e49880", "e49622", "e49571", "e51077", "e49577",
                         "e49595", "e50784", "e49598", "e49596", "e49575", "e49527",
                         "e49576", "e49572", "e49562", "e49621", "e49887", "e49593",
                         "e49591", "e49592", "e49603", "e49547", "e49605", "e41049",
                         "e51098", "e49612", "e49610", "e49615", "e49618", "e49889",
                         "e49619", "e49620", "e49609", "e49570", "e49597", "e49594",
                         "e50655", "e51725", "e39964", "e40003", "e40005", "e40023",
                         "e40024", "e40007", "e39999", "e50656", "e39992", "e41356",
                         "e41357", "e41359", "e41358", "e50795", "e50713", "e51666",
                         "e49528", "e51213"
                         );

$context = lc $context;
if (length $libraryurl < 1) {
    print "Library URL was not provided\n";
}
else {
   $libraryurl =~ s/\/$//gis;
   $libraryurl = $libraryurl."/";
}

if ( length $folder < 1 || length $library_partnumber < 1 ) {
    print "----------------------------------------\n";
    print "Error: Incorrect Number of Arguments passed.\n";
    print "----------------------------------------\n";
    print "Usage:\n";
    print
        "perl analyzer_elastic_json.pl -f <FOLDER> -l <LIB PART NUMBER> --ctx <CONTEXT> -u <LIBRARY-URL>\n";
    print "----------------------------------------\n";
    exit;
}

my $snapshot_date = snapshot_time();

# take backup
# delete the index
# create a new index with the same name
# put mapping in a mapping file
# create the json data in a separate json file

my $elastic_index = <<"TOP";

curl -sS -XPUT "${server_elastic_search}:9200/_snapshot/docsbackup/${context}_${snapshot_date}" -d '{
    "indices": "${context}",
    "ignore_unavailable": "true",
    "include_global_state": false
}'

VIVEK-SAMPLE

curl -sS -XDELETE 'http://${server_elastic_search}:9200/${context}'

VIVEK-SAMPLE

curl -sS -XPUT 'http://${server_elastic_search}:9200/${context}/'

VIVEK-SAMPLE

curl -sS -XPUT "${server_elastic_search}:9200/${context}/_settings -d '{"index" : {"refresh_interval" : "-1", "number_of_replicas" : "0"}}'


TOP

my %index_type_mappings = ();

my @errorlines = ();

if ( !-d $folder ) {
    print "The Supplied folder path does not exist or is not a folder.\n";
    exit;
}
my @dir                  = ();
my @titlefiles           = ();
my %targets              = ();
my $time                 = time;
my $check_date           = localtime time;
my $count_chunks         = 0;
my $summary_count        = 0;
my $stdocid              = q();
my $track                = 0;
my $ignore_track         = 0;
my @bar                  = ( '|', '/', '--', '|', '--', '\\', );
my $head                 = q();
my $body                 = q();
my @allids               = ();
my $lastidused           = ();
my @cleanedlines         = ();
my $chunk                = q();
my $wasadded             = q(0);
my $largeprint           = 0;
my $output_folder        = q(./output);
my $lastchunkwritten     = q();
my $isPSFT               = q();
my @headclasses
    = qw/msg glossaryentry glossaryterm glossterm titleinequation itemizedlisttitle orderedlisttitle segmentedlisttitle variablelisttitle/;
    # titleinrefsubsect titleinrefsubsect2 titleinrefsubsect3
    # titleinfigure titleinexample bridgehead subhead1 subhead2 subhead3
my @tabletitleclass
    = qw/titleintable/;

my @donotbreakat_class = qw/tblformal tblformalwide titleinrefsubsect Formal NoteAlso Note titleinfigure titleinexample bridgehead subhead1 subhead2 subhead3 example sect3 sect4 sect5/;
#titleinfigure titleinexample bridgehead subhead1 subhead2 subhead3 added to do not break classes as per DPS-3072. Also restricted the H element to 1 2 3
my @donotbreakat_id_regex = ('^[A-Z]{8, }$');

my $chaptertitle      = q();
my $chunkclass        = q();
my $chunkheadlevel    = q();
my $last_id_found     = q();
my %booktitle         = ();
my %topic_types_found = ();
my $file_release_date = q();
my $file_description  = q();
my $pointer_description  = q();
my $file_keywords     = q();
my $book_formats      = q();
$OUTPUT_AUTOFLUSH++;

find( { wanted => \&wanted, no_chdir => 1 }, $folder );
if ( scalar @dir < 1 ) {
    print "Error: no htm(l) file found.\n";
    exit;
}

if (-d $output_folder) {
    print "Output folder already present.";
    ##exit;
}

if ( !-d $output_folder ) {
    mkdir $output_folder;
}

my $jsonoutputfolder = $output_folder . q(/json);

if ( !-d $jsonoutputfolder ) {
    mkdir $jsonoutputfolder;
}

if ( -f $jsonoutputfolder . q(/) . $library_partnumber . q(.txt) ) {
    ##unlink $jsonoutputfolder . q(/) . $library_partnumber . q(.txt);
}

open my $CHUNK, '>>', $jsonoutputfolder . q(/) . $library_partnumber . q(-mapping.txt)
    or croak "Couldnt write to json output file: $OS_ERROR\n";
binmode $CHUNK, ':encoding(UTF-8)';
print {$CHUNK} $elastic_index . "\n\n";
print {$CHUNK} q(VIVEK-SAMPLE) . "\n\n";
close $CHUNK
    or carp "Cant close: $OS_ERROR";

build_data( $library_partnumber, $folder );

my $json_title_lib   = q();
my $json_release_lib = q();
if ( exists $library_data{$library_partnumber} ) {
    $json_title_lib = $library_data{$library_partnumber}[0];
    $json_release_lib
        = $library_data{$library_partnumber}[$SHORTCUT_CHAR_LENGTH_FIVE];
}
else { $json_title_lib = q(Not Available.); }
my $file_lang = q(en);
$isPSFT = q(0);
my $javadoc = q(0);
my $ignoretableprocessing = q(0);
my $thisfilechunkcount = 0;
my $noid = q(0);
my $isversionof = q();
foreach my $file (@dir) {
    $noid = q(0);
    $isversionof = q();
    tidyhtml($file);
    $thisfilechunkcount = 0;
    $book_formats = q();
    $file_lang = q(en);
    $file_release_date = q();
    $file_description  = q();
    $pointer_description  = q();
    $file_keywords     = q();
    $javadoc = q(0);

    $track++;
    my @file_content           = ();
    my $current_id             = q();
    my $last_id                = q();
    my $id_related_text        = q();
    my $equivalent_data_holder = q();
    $chaptertitle = q();
    my $file_path = $file;
    $file_path =~ s/\\/\//gis;
    $file_path =~ s/(.*)\/(.*)/$1/gis;

    my $file_name_val = $file;
    $file_name_val =~ s/\\/\//gis;
    $file_name_val =~ s/(.*)\/(.*)/$2/gis;

    my $fname_processed = $file_path;
    if ( $fname_processed =~ m/(.*)\/(.*)/gis ) {
        $fname_processed = $2 . q(/) . $file_name_val;
    }

    # format Print
    ###########################################################################
   #my $log_print = "$track out of ".scalar (@dir)." files ".$bar[$track % 6];
    if ( $largeprint == 0 ) {
        $largeprint = length $fname_processed;
    }
    if ( $largeprint < length $fname_processed ) {
        $largeprint = length $fname_processed;
    }
    if ( length $fname_processed < $largeprint ) {
        my $space = q();
        for (
            my $spacer = 0;
            $spacer < (
                $SHORTCUT_CHAR_LENGTH_THIRTYFIVE - ( length $fname_processed )
            );
            $spacer++
            )
        {
            $space .= q( );
        }
        $fname_processed .= $space;
    }
    my $log_print = $track . q( out of ) . scalar @dir . q( files );
    printf qq[\r$log_print $fname_processed\t];
    ###########################################################################

    open my $FILE, '<', $file
        or croak "Error while reading $file: $OS_ERROR";
    #binmode $FILE, ':encoding(ISO-8859-1)';
    #binmode $FILE, ':encoding(UTF-8)';
    #binmode $FILE;
    @file_content = <$FILE>;
    close $FILE
        or carp "Can't close file: $OS_ERROR";

    # new way
    my $filejoined = join " ", @file_content;
    ##print "DEBUG: Pass 012\n";
    undef @file_content;
    if (   $filejoined =~ m{ <[?]xml [^>]+ encoding [[:space:]]* = [[:space:]]* ['"] utf -? 8 }xmsi
        || $filejoined =~ m{ <meta [^>]+ charset [[:space:]]* = [[:space:]]* utf -? 8 }xmsi )
    {
        $filejoined = Encode::decode( 'utf8', $filejoined );
    }
    else {
        $filejoined = properly_decode($filejoined);
    }

    #elsif (   $filejoined =~ m{ <[?]xml [^>]+ encoding [[:space:]]* = [[:space:]]* ['"] (.*?) ['"]}xmsi
    #    || $filejoined =~ m{ <meta [^>]+ charset [[:space:]]* = [[:space:]]* ['"] (.*?) ['"] }xmsi
    #) {
    #    my $charencodingfound = $1;
    #    $charencodingfound =~ s/^(\s)+//gis;
    #    $charencodingfound =~ s/(\s)+$//gis;
    #    $filejoined = decode( $1, $filejoined );
    #}
    #else {
    #    $filejoined = decode( 'utf8', $filejoined );
    #    # html/securityroles.htm
    #}

    if ( $filejoined =~ m/<title>(.*?)index(.*?)<\/title>/is) {
        next;
    }
    # exclude indexing if the file has noindex for robots
    if ( $filejoined =~ m/<meta(\s)*name(\s)*=(\s)*"robots"(\s)*content(\s)*=(\s)*"([^"]*)noindex([^"]*)"([^>]*)>/is) {
        $ignore_track++;
        next;
    }
    ##print "DEBUG: Pass 01\n";
    # get the formats from the head elements
    if ($filejoined =~ m/<link(\s)*rel(\s)*=(\s)*"alternate"(\s)*href(\s)*=(\s)*"([^"]+)"(\s)*title="([^>]+)"(\s)*type(\s)*=(\s)*"application\/pdf"([^>]*)>/i) {
        $book_formats .= $7.";";
    }
    if ($filejoined =~ m/<link(\s)*rel(\s)*=(\s)*"alternate"(\s)*href(\s)*=(\s)*"([^"]+)"(\s)*title="([^>]+)"(\s)*type(\s)*=(\s)*"([^"]*)epub([^"]*)"([^>]*)>/i) {
        $book_formats .= $7.";";
    }
    if ($filejoined =~ m/<link(\s)*rel(\s)*=(\s)*"alternate"(\s)*href(\s)*=(\s)*"([^"]+)"(\s)*title="([^>]+)"(\s)*type(\s)*=(\s)*"([^"]*)mobi([^"]*)"([^>]*)>/i) {
        $book_formats .= $7.";";
    }
    #print "$book_formats\n";
    ##print "DEBUG: Pass 013\n";

    ## First pass: Check if there are any name or id that can be used else we will need to get all the content and link it
    pos( $filejoined ) = 0;
    if ($filejoined !~ m/id(\s)*=(\s)*"([^"]+)"/gis && $filejoined !~ m/<a([^>]+)name(\s)*=(\s)*"([^"]+)"([^>]*)>/gis) {
        $filejoined =~ s/(<body([^>]*)>)/$1\n<a id="JUSTANID" \/>/is;
        $noid = q(1);
    }
    ##print "DEBUG: Pass No id: $noid\n";

    ##if (length $book_formats > 0) {
    ##    my @ot_formats = split(/;/, $book_formats);
    ##    $book_formats = q();
    ##    my $bpath = $file;
    ##    $bpath =~ s/\\/\//gis;
    ##    $bpath =~ s/(.*)\/(.*)/$1/gis;
    ##    foreach my $fr (@ot_formats) {
    ##      if (length $fr > 0) {
    ##        #print "Add: $bpath, $fr";
    ##        $fr = calculate_path($bpath, $fr);
    ##        $fr =~ s/\\/\//gisxm;
    ##        if (length $fr > 0) {
    ##          $book_formats .= $fr.";";
    ##        }
    ##      }
    ##    }
    ##}

    pos( $filejoined ) = 0;
    ##print "DEBUG: Pass 014\n";
    if ( $filejoined =~ m/<title>(.*?)<\/title>/is ) {
      my $whattitle = $1;
      if ( $whattitle =~ m/API/is
        || $whattitle =~ m/xml\s*schema/is
        || $whattitle =~ m/java/is
        || $whattitle =~ m/Generated(\s)by(\s)javadoc/is
      ) {
        $javadoc = q(1);
      }
      if ( $whattitle =~ m/reference(\s)+manual/is) {
        $ignoretableprocessing = q(1);
      }
    }
    ##if ( $filejoined =~ m/<title>(.*?)(\s)API(.*?)<\/title>/is
    ##    || $filejoined =~ m/<title>(.*?)xml\s*schema\s*(.*?)<\/title>/is
    ##    || $filejoined =~ m/<title>(.*?)java(.*?)<\/title>/is
    ##    || $filejoined =~ m/Generated(\s)by(\s)javadoc/is
    ##) {
    ##    $javadoc = q(1);
    ##}

    ##if ( $filejoined =~ m/<title>(.*?)reference(\s)+manual(.*?)<\/title>/is) {
    ##    $ignoretableprocessing = q(1);
    ##}
    pos( $filejoined ) = 0;
    ##print "DEBUG: Pass 014q\n";

    if ($javadoc eq q(1)) {
        ##print "DEBUG: Pass 014-1\n";
        $filejoined =~ s/(<body([^>]*)>)(.*?)(<div(\s)*class(\s)*=(\s)*"header"([^>]*)>)/$1$4/is;
    }
    elsif ($filejoined !~ m/index[.]html$/) {
        ##print "DEBUG: Pass 014-31\n";
        $filejoined =~ s/(<body([^>]*)>)(.*?)(<div([^>]*?)id(\s)*=(\s)*"header"([^>]*)>)/$1$4/is;
        ##print "DEBUG: Pass 014-32\n";
        $filejoined =~ s/(<body([^>]*)>)(.*?)(<div([^>]*?)class(\s)*=(\s)*"header"([^>]*)>)/$1$4/is;
        ##print "DEBUG: Pass 014-33\n";
        if ($filejoined =~ m/class(\s)*=(\s)*"ind"/is) {
                   $filejoined =~ s/(<div(\s)*class(\s)*=(\s)*"header"([^>]*)>)(.*?)(<div(\s)*class(\s)*=(\s)*"ind">)/$1$7/is;
        }
        ##print "DEBUG: Pass 014-34\n";
    }
    ##print "DEBUG: Pass 015\n";

    if ( $filejoined =~ m/lang="([^"]+)"/isxm ) {
        $file_lang = $1;
        if (lc $file_lang eq q(en-us)) {$file_lang = q(en);}
        if (lc $file_lang eq q(en.us)) {$file_lang = q(en);}
    }
    elsif ($filejoined =~ m/xml:lang="([^"]+)"/isxm) {
        $file_lang = $1;
        if (lc $file_lang eq q(en-us)) {$file_lang = q(en);}
        if (lc $file_lang eq q(en.us)) {$file_lang = q(en);}
    }

    ##print "DEBUG: Pass 1\n";
    Readonly my $REGEXA => qr{ <div(\s)+class(\s)*=(\s)*"container"> }xms;
    Readonly my $REGEXB => qr{ <div(\s)+class(\s)*=(\s)*"bodyContent"> }xms;
    if ( $filejoined =~ m/$REGEXA(.*)$REGEXB/gis ) {
        $filejoined =~ s/($REGEXA)(.*)($REGEXB>)/$1$6/gis;
    }

    ##print "DEBUG: Pass 2\n";
    pos( $filejoined ) = 0;
    if ( $filejoined =~ m/<A(\s)+NAME(\s)*=(\s)*"navbar_bottom">/gis ) {
        $filejoined =~ s/<A(\s)+NAME(\s)*=(\s)*"navbar_bottom">(.*)//gis;
    }

    Readonly my $REGEXC => qr{ <A(\s)+NAME(\s)*=(\s)*"navbar_top"> }xms;
    Readonly my $REGEXD =>
        qr{ <A(\s)+NAME(\s)*=(\s)*"skip-navbar_top"><\/A> }xms;
    pos( $filejoined ) = 0;
    if ( $filejoined =~ m/$REGEXC(.*)$REGEXD/gis ) {
        $filejoined =~ s/$REGEXC(.*)$REGEXD//gis;
    }

    pos( $filejoined ) = 0;
    if ( $filejoined =~ m/<div(\s)+class(\s)*=(\s)*"FootBookNav">/gis ) {
        $filejoined =~ s/<div(\s)+class(\s)*=(\s)*"FootBookNav">(.*)//gis;
    }

    Readonly my $REGEXEF =>
        qr{ <div(\s)+class(\s)*=(\s)*"zz-skip-header"> }xms;
    Readonly my $REGEXE =>
        qr{ $REGEXEF<a([^>]+)>Skip(\s)+Headers<\/a><\/div> }xms;
    pos( $filejoined ) = 0;
    while ( $filejoined =~ m/($REGEXE)/gis ) {
        $filejoined =~ s/\Q$1\E//gis;
    }

    if ( $filejoined =~ m/(<div(\s)+class(\s)*=(\s)*"footer">(.*?)<\/div>)/gis ) {
        $filejoined =~ s/\Q$1\E(.*)//gis;
    }
    if ( $filejoined =~ m/(<div(\s)+id(\s)*=(\s)*"footer">(.*?)<\/div>)/gis ) {
        $filejoined =~ s/\Q$1\E(.*)//gis;
    }
    if ( $filejoined =~ m/(<div(\s)+id(\s)*=(\s)*"RIGHTCOLUMN">(.*?)<\/div>)/gis ) {
        $filejoined =~ s/\Q$1\E(.*)//gis;
    }
    ##print "DEBUG: Pass 3\n";

    pos( $filejoined ) = 0;
    $filejoined =~ s/(<span(\s)+class(\s)*=(\s)*"icon">([^<]+)<\/span>)//gis;
    
    Readonly my $REGEXFCLASS =>
        qr{ class[\s]*=[\s]*"simple[\s]*oac_no_warn" }xms;
    Readonly my $REGEXFA =>
        qr{ $REGEXFCLASS[\s]*summary=""[\s]*cellspacing="0" }xms;
    Readonly my $REGEXF =>
        qr{ <table[\s]*$REGEXFA[\s]*cellpadding="0"[\s]*width="150"> }xms;
    pos( $filejoined ) = 0;
    $filejoined =~ s/($REGEXF(.*?)<\/table>)//gis;

    ##print "DEBUG: Pass 4\n";

    Readonly my $REGEXG =>
        qr{ <table[\s]*$REGEXFA[\s]*cellpadding="0"[\s]*width="100"> }xms;
    pos( $filejoined ) = 0;
    while ( $filejoined =~ m/($REGEXG(.*?)<\/table>)/gis ) {
        $filejoined =~ s/\Q$1\E//gis;
    }

    Readonly my $REGEXH =>
        qr{ <table[\s]*$REGEXFA[\s]*cellpadding="0"[\s]*width="(.*?)"> }xms;
    pos( $filejoined ) = 0;
    while ( $filejoined =~ m/($REGEXH(.*?)<\/table>)/gis ) {
        $filejoined =~ s/\Q$1\E//gis;
    }

    Readonly my $REGEXI =>
        qr{ <p(\s)+class(\s)*=(\s)*"betadraftsubtitle"> }xms;
    pos( $filejoined ) = 0;
    while (
        $filejoined =~ m/(($REGEXI)(.*?)Beta[\s]*Draft:([^<]+)<\/p>)/gis )
    {
        $filejoined =~ s/\Q$1\E//gis;
    }
    ##print "DEBUG: Pass 5\n";

    pos( $filejoined ) = 0;
    if ($filejoined =~ m/(<img(\s)+src(\s)*=(\s)*"([.\/]+)(dcommon)([^>]+)>)/i) {
      $filejoined =~ s/(<img(\s)+src(\s)*=(\s)*"([.\/]+)(dcommon)([^>]+)>)//gis;
    }
    ##print "DEBUG: Pass 5.1\n";

    pos( $filejoined ) = 0;
    if ($filejoined =~ m/(<script([^>]*)>(.*?)<\/script>)/is) {
        $filejoined =~ s/(<script([^>]*)>(.*?)<\/script>)//gis;
    }
    pos( $filejoined ) = 0;
    if ($filejoined =~ m/(<noscript([^>]*)>(.*?)<\/noscript>)/is) {
        $filejoined =~ s/(<noscript([^>]*)>(.*?)<\/noscript>)//gis;
    }

    ##pos( $filejoined ) = 0;
    ##if ($filejoined =~ m/(<span(\s)*class(\s)*=(\s)*"secnum"([^>]*)>(.*?)<\/span>)/is) {
    ##    $filejoined =~ s/(<span(\s)*class(\s)*=(\s)*"secnum"([^>]*)>(.*?)<\/span>)//gis;
    ##}

    ##print "DEBUG: Pass 5.1.1\n";

    pos( $filejoined ) = 0;
    if ($filejoined =~ m/<div(\s)*([^>]*)id(\s)*=(\s)*"skiptocontent"([^>]*)>(.*?)<\/div>/gis){
        $filejoined =~ s/<div(\s)*([^>]*)id(\s)*=(\s)*"skiptocontent"([^>]*)>(.*?)<\/div>//gis;
    }
    ##print "DEBUG: Pass 5.1.2\n";
    pos( $filejoined ) = 0;
    if ($filejoined =~ m/<div(\s)*([^>]*)class(\s)*=(\s)*"skiptocontent"([^>]*)>(.*?)<\/div>/gis){
        $filejoined =~ s/<div(\s)*([^>]*)class(\s)*=(\s)*"skiptocontent"([^>]*)>(.*?)<\/div>//gis;
    }
    ##print "DEBUG: Pass 5.1.3\n";

    pos( $filejoined ) = 0;
    if ($filejoined =~ m/(<style([^>]*)>(.*?)<\/style>)/is) {
        $filejoined =~ s/(<style([^>]*)>(.*?)<\/style>)//gis;
    }
    ##print "DEBUG: Pass 5.2\n";

    if ($filejoined =~ m/<meta(.*?)name(\s)*=(\s)*"dcterms.isVersionOf"(.*?)content(\s)*=(\s)*"([^"]+)"/is) {
        $isversionof = $7;
    }

    if ($isPSFT ne q(1) && $filejoined =~ m/<meta(.*?)content(\s)*=(\s)*"peoplesoft(.*)/is) {
        $isPSFT = q(1);
    }
    ##print "DEBUG: Pass 5.3\n";

    if ($filejoined =~ m/<meta(.*?)name(\s)*=(\s)*"date"(\s)*content(\s)*=(\s)*"([^"]+)"/is)
    {
        $file_release_date = get_correct_date_format($7);
    }
    if ($filejoined =~ m/<meta(.*?)name(\s)*=(\s)*"dcterms.created"(\s)*content(\s)*=(\s)*"([^"]+)"/is)
    {
        $file_release_date = get_correct_date_format($7);
    }
    ##print "DEBUG: Pass 5.3.1\n";
    if ($filejoined =~ m/<meta(.*?)name(\s)*=(\s)*"description"(\s)*content(\s)*=(\s)*"([^"]+)"/is)
    {
        $file_description = $7;
    }
    ##print "DEBUG: Pass 5.3.1-1\n";
    if ($filejoined =~ m/<meta(.*?)name(\s)*=(\s)*"keyword"(\s)*content(\s)*=(\s)*"([^"]+)"/is)
    {
        $file_keywords = $7;
    }

    ##print "DEBUG: Pass 5.3.1-2\n";
    pos( $filejoined ) = 0;
    if ($javadoc ne "1"){
        $filejoined =~ s/(<div(\s)+class(\s)*=(\s)*"container">)(.*?)(<div(\s)+class(\s)*=(\s)*"bodyContent")>/$1$6/is;
    }
    ##print "DEBUG: Pass 6\n";
    ##pos( $filejoined ) = 0;
    ##print "DEBUG: Pass 5.3.1-3\n";
    if ($javadoc eq  "1") {
      $filejoined =~ s/<A(\s)+NAME(\s)*=(\s)*"navbar_bottom">(.*)//is;    
    }
    ##print "DEBUG: Pass 6.0.1\n";

    if ($javadoc ne "1" && $file !~ m/index.htm/ && $filejoined =~ m/<article/is) {
      $filejoined =~ s/<body([^>]*)>(.*?)<article([^>]*)>/<body><article>/is;
    }

    if ($javadoc ne "1" && $file !~ m/index.htm/ && $filejoined =~ m/<article>/is) {
      pos( $filejoined ) = 0;
      $filejoined =~ s/(.*?)<body>(.*?)<article>(.*?)<\/article>(.*?)/$1<body>$2<article>$3<\/article>/is;
    }
    ##print "DEBUG: Pass 6.1\n";
    Readonly my $REGEXJA => qr{ align="right"(\s)+style="width:120px; }xms;
    Readonly my $REGEXJB => qr{ float:right;(\s)*padding-right:5px; }xms;
    Readonly my $REGEXJC =>
        qr{ padding-top:4px;(\s)*right:2px;(\s)*display:inline;" }xms;
    Readonly my $REGEXJ =>
        qr{ <div(\s)+$REGEXJA(\s)+$REGEXJB(\s)*$REGEXJC> }xms;
    Readonly my $REGEXPDF =>
        qr{ <a(\s)+href="[.][.]\/([[:upper:]]{5})[.]pdf">\[PDF\]<\/a> }xms;
    Readonly my $REGEXMOBI =>
        qr{ <a(\s)+href="[.][.]\/([[:upper:]]{5})[.]mobi">\[Mobi\]<\/a> }xms;
    Readonly my $REGEXEPUB =>
        qr{ <a href="[.][.]\/([[:upper:]]{5})[.]epub">\[ePub\]<\/a> }xms;
    Readonly my $REGEXK =>
        qr{ $REGEXPDF(\s)*$REGEXMOBI(\s)+$REGEXEPUB<br \/>([^<]+)<\/div> }xms;
    pos( $filejoined ) = 0;

    if ( $javadoc ne q(1) && $filejoined =~ m/<a href="[.][.]\/([[:upper:]]{5})[.]epub">\[ePub\]<\/a>/is) {
        $filejoined =~ s/$REGEXJ$REGEXK//is;
    }
    ##print "DEBUG: Pass 7: \n";

    pos( $filejoined ) = 0;

    if ($noid ne "1" && $javadoc ne "1" && $file !~ m/index.html$/) {

            $filejoined =~ s/(<div\s*\s*id=\s*"BREADCRUMBS">)(.*?)<\/div>//is;
            ##print "DEBUG: Pass 7.1: \n";

            $filejoined =~ s/(<span\s*id\s*=\s*"PAGE"([^>]*)>)(.*?)<\/span>//is;
            ##print "DEBUG: Pass 7.1: \n";

            $filejoined =~ s/(<span(\s)*class(\s)*=(\s)*"page"([^>]*)>(.*?)<\/span>)//is;
            ##print "DEBUG: Pass 7.1: \n";

            $filejoined =~ s/(<body([^>]*)>)(.*?)(<div(\s)*class(\s)*=(\s)*"pagePane([^"]*)">)/$1$4/gis;
            ##print "DEBUG: Pass 7.1: \n";

            $filejoined =~ s/<img([^>]*)>//gis;
            ##print "DEBUG: Pass 7.2: \n";

            $filejoined =~ s/(<body([^>]*)>)(.*?)(<div(\s)*class(\s)*=(\s)*"ContentPane">)/$1$4/gis;
            ##print "DEBUG: Pass 7.3: \n";

            $filejoined =~ s/<div(\s)+align="right"(\s)+style="width:120px;(\s)+float:right;(\s)*padding-right:5px;(\s)*padding-top:4px;(\s)*right:2px;(\s)*display:inline;"><a(\s)+href="\.\.\/([A-Z]{5})\.pdf">\[PDF\]<\/a>(\s)*<a(\s)+href="\.\.\/([A-Z]{5}).mobi">\[Mobi\]<\/a>(\s)+<a href="\.\.\/([A-Z]{5})\.epub">\[ePub\]<\/a><br \/>([^<]+)<\/div>//gs;
            ##print "DEBUG: Pass 7.4: \n";
            ####
            if ($filejoined =~ m/"articlewrapper"/gis) {
              $filejoined =~ s/(<body([^>]*)>)(.*?)(<div([^>]*)class(\s)*=(\s)*"articlewrapper"([^>]*)>)/$4/gis;
              $filejoined =~ s/(<div(\s)*id(\s)*=(\s)*"rightslider">)(.*?)(<div([^>]*)class(\s)*=(\s)*"articlewrapper"([^>]*)>)/$6/gis;
            }
            ##print "DEBUG: Pass 7.4.1: \n";
            ##print "DEBUG: Pass 7.5: \n";

            if ($filejoined =~ m/"panellists"/is) {
              $filejoined =~ s/(<div(\s)+class(\s)*=(\s)*"panellists">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.6: \n";

            if ($filejoined =~ m/"breadcrumb"/is) {
              $filejoined =~ s/(<div(\s)+id(\s)*=(\s)*"breadcrumb">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.7: \n";

            if ($filejoined =~ m/"bookoptions"/is) {
              $filejoined =~ s/(<div(\s)+class(\s)*=(\s)*"bookoptions">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.8: \n";

            if ($filejoined =~ m/"pagenav"/is) {
              $filejoined =~ s/(<div(\s)+id(\s)*=(\s)*"pagenav">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.9: \n";

            if ($filejoined =~ m/"contentarea(\s+)clearboth"/is) {
              $filejoined =~ s/(<div(\s)+class(\s)*=(\s)*"contentarea(\s+)clearboth">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.10: \n";

            if ($filejoined =~ m/"altlogo"/is) {
              $filejoined =~ s/(<div(\s)+id(\s)*=(\s)*"altlogo">(.*?)<\/div>)//gis;
            }

            ##print "DEBUG: Pass 7.11: \n";

            if ($filejoined =~ m/"searchheader"/is) {
              $filejoined =~ s/(<div(\s)+id(\s)*=(\s)*"searchheader">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.12: \n";

            if ($filejoined =~ m/"signInArea"/is) {
              $filejoined =~ s/(<div(\s)+id(\s)*=(\s)*"signInArea">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.13: \n";

            if ($filejoined =~ m/<header/is) {
              $filejoined =~ s/(<header(.*?)>(.*?)<\/header>)//is;
            }

            ##print "DEBUG: Pass 7.14: \n";

            if ($filejoined =~ m/"tw-like"/is) {
              $filejoined =~ s/(<div(\s)+id="tw-like">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.15: \n";

            if ($filejoined =~ m/"g-plusone"/is) {
              $filejoined =~ s/(<div(\s)+class="g-plusone"(.*?)>(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.16: \n";

            if ($filejoined =~ m/"go-like"/is) {
              $filejoined =~ s/(<div(\s)+id="go-like">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.17: \n";

            if ($filejoined =~ m/"fb-root"/is) {
              $filejoined =~ s/(<div(\s)+id="fb-root">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.18: \n";

            if ($filejoined =~ m/"fb-like"/is) {
              $filejoined =~ s/(<div(\s)+id="fb-like">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.19: \n";

            if ($filejoined =~ m/"SocialBar"/is) {
              $filejoined =~ s/(<div(\s)+class="SocialBar">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.20: \n";

            if ($filejoined =~ m/"footer-containerbook/is) {
              $filejoined =~ s/(<div(\s)+class(\s)*=(\s)*"footer-containerbook(.*?)">(.*?)<\/div>)//is;
            }
            ##print "DEBUG: Pass 7.21: \n";

            if ($filejoined =~ m/"socialicons"/is) {
              $filejoined =~ s/(<div(\s)+class(\s)*=(\s)*"socialicons">(.*?)<\/div>)//gis;
            }
            ##print "DEBUG: Pass 7.22: \n";

            $filejoined =~ s/(<footer>(.*?)<\/footer>)//is;
            ##print "DEBUG: Pass 7.23: \n";

            if ($filejoined =~ m/"socialicons"/is) {
              $filejoined =~ s/(<div(\s)+class(\s)*=(\s)*"socialicons">(.*?)<\/div>)//gis;
            }
            if ($filejoined =~ m/"indexterm-anchor"/is) {
              $filejoined =~ s/(<a(\s)*id(\s)*=(\s)*"([^"])+"(\s)*class(\s)*=(\s)*"indexterm-anchor"><\/a>)//gis;
            }
            ####print "DEBUG: PASS 1: $filejoined\n\n";

            if ($filejoined =~ m/"footer"/is) {
              $filejoined =~ s/<div(\s)*class(\s)*=(\s)*"footer">(.*)//is;
              ##print "DEBUG: Pass 7.24: \n";

              $filejoined =~ s/<div(\s)*id(\s)*=(\s)*"footer">(.*)//is;
              ##print "DEBUG: Pass 7.25: \n";
            }

            if ($filejoined =~ m/"booktitle"/is) {
              $filejoined =~ s/(<div(\s)+class(\s)*=(\s)*"booktitle">(.*?)<\/div>)//is;
            }

            ##print "DEBUG: Pass 7.26: \n";
            if ($filejoined =~ m/<div(\s)*class(\s)*=(\s)*"ind">/is) {
                $filejoined =~ s/(<body([^>]+)>)(.*?)(<div(\s)*class(\s)*=(\s)*"ind">)/$1$4/is;
            }
            ##print "DEBUG: Pass 7.27: \n";
            if ($isPSFT eq q(1)) {
              $filejoined =~ s/<span(\s)*class(\s)*=(\s)*"PTTRANSPARENT"(\s)*([^>]*)>(.*?)<\/([^>]+)>//gis;  
            }
            ##print "DEBUG: Pass 7.28: \n";
    }
    ### Process tables first
    ##print "DEBUG: Pass 8\n";


    if ( $tableprocessing && $noid ne "1" && $javadoc ne "1" && $filejoined =~ m/<table/gis ) {
        while ( $filejoined =~ m/((<table.*?>)(.*?)<\/table>)/gis ) {
            my $howmanytablechunks = 0;
            my $this_table = $1;
            my $original_table_content = $3;
            $original_table_content =~ s/<tbody([^>]*)>//gis;
            $original_table_content =~ s/<\/tbody>//gis;
            ##print "DEBUG: Pass 8.1\n";
            # find the ids and append as a id before it
            my $idstreamtable
                = HTML::TokeParser->new( \$original_table_content )
                or carp "Couldn't parse: $OS_ERROR\n";
            my $tableid     = q();
            my $thishead    = q();
            my $thistabsumm = q();
            while ( my $tabletoken = $idstreamtable->get_token() ) {
                if ( $tabletoken->[0] eq q(S)
                    && exists $tabletoken->[2]{'id'} )
                {
                    if (   length $tableid > 0
                        && length $thishead > 0
                        && length $thistabsumm > 0
                        && verify_chunk( $thishead, $thistabsumm ) == 1
                    )
                    {
                        $thistabsumm =~ s/(\s)+$//gis;
                        my $stdocida  = $tableid;
                        my $chunkname = $file_name_val . q(-) . $stdocida;
                        $count_chunks++;
                        $howmanytablechunks++;
                        chunk_manager(
                            $file,
                            $stdocida,
                            $file_path . q(/) . $chunkname,
                            q(),
                            q(<head>) . $thishead . q(</head>),
                            $thistabsumm,
                            q(),
                            q()
                        );
                        $tableid     = q();
                        $thishead    = q();
                        $thistabsumm = q();

                    }

                    # this is the head
                    $tableid  = $tabletoken->[2]{'id'};
                    $thishead = $idstreamtable->get_trimmed_text(
                        q(/) . $tabletoken->[1] );
                    $thishead =~ s/^( )+//gis;
                    $thishead =~ s/( )+$//gis;
                }
                elsif (
                    $tabletoken->[0] eq 'S'
                    && (   $tabletoken->[1] eq q(td)
                        || $tabletoken->[1] eq q(th) )
                    )
                {
                    my $thiscell = $idstreamtable->get_trimmed_text(q(/) . $tabletoken->[1] );

                    # check if the heading was just a numbering

                    if ($thishead =~ m/^[\s\d.]+$/i) {
                        $thishead = $thishead.q( ).$thiscell;
                    }
                    elsif (length($thishead) < 1) {
                        $thishead = $thiscell;
                    }
                    else {
                        $thistabsumm
                          .= $thiscell . q( );
                    }
                    #$thistabsumm
                    #    .= $thiscell . q( );
                }
            }
            if (   length $tableid > 0
                && length $thishead > 0
                && length $thistabsumm > 0
                && verify_chunk( $thishead, $thistabsumm ) == 1
            )
            {
                $thistabsumm =~ s/(\s)+$//gis;
                my $stdocida  = $tableid;
                my $chunkname = $file_name_val . q(-) . $stdocida;
                $count_chunks++;
                $howmanytablechunks++;
                chunk_manager(
                    $file,
                    $stdocida,
                    $file_path . q(/) . $chunkname,
                    q(),
                    q(<head>) . $thishead . q(</head>),
                    $thistabsumm,
                    q(),
                    q()
                );
                $tableid     = q();
                $thishead    = q();
                $thistabsumm = q();
            }
        }
    }

    ## check if the table remains, if yes extract only the text

    # remove the tablefootnote, titleintable
    ##print "DEBUG: Pass 8.1\n";
    pos( $filejoined ) = 0;
    $filejoined
        =~ s/<p(\s)*class(\s)*=(\s)*"tablefootnote"([^>]*)>(.*?)<\/p>//gis;

    pos( $filejoined ) = 0;
    ##$filejoined =~ s/<p(\s)*class(\s)*=(\s)*"titleintable"([^>]*)>(.*?)<\/p>//gis;
    ##print "DEBUG: Pass arranging\n";
    undef @cleanedlines;
    arrange( $filejoined, $file );
    ##print "DEBUG: arranged\n";
    ##@cleanedlines = @file_content;
    ##@file_content = ();

    $lastchunkwritten = q();
    my $countChunks = 0;
    for (
        my $linenumber = 0;
        $linenumber < scalar @cleanedlines;
        $linenumber++
        )
    {
        ####print "DEBUG: LINE: ".$cleanedlines[$linenumber]."\n";
        if ($cleanedlines[$linenumber] =~ m/<[h]/i) {
            $cleanedlines[$linenumber] =~ s/<a(\s)*([^>])*id(\s)*=(\s)*"sthref[0-9]+"([^>])*>(<\a>)*//;
            $cleanedlines[$linenumber] =~ s/<a(\s)*([^>])*id(\s)*=(\s)*"sthref[0-9]+"([^>])*>(<\/a>)*//gis;
            $cleanedlines[$linenumber] =~ s/(<span(\s)*([^>])*class(\s)*=(\s)*"italic"([^>])*>)(.*?)(<\/span>)/$7/gis;
        }
        $wasadded             = q();
        my $idstream = HTML::TokeParser->new( \$cleanedlines[$linenumber] )
            or carp "Couldn't parse: $OS_ERROR";

        while ( my $token = $idstream->get_token() ) {
            if ($token->[0] eq 'T') {
              ## deal with the case when line is only a text
              if ($cleanedlines[$linenumber] !~ m/<[A-Z]+([^>])*>/gis && $cleanedlines[$linenumber] !~ m/<\/[A-Z]+([^>])*>/gis) {
                $chunk .= $cleanedlines[$linenumber] . "\n";
                $wasadded = q(1);
                last;
              }
              next;
            }
            if ($ignoretableprocessing ne q(1) && $cleanedlines[$linenumber] =~ m/<tr[^>]*>/gis) {
              $cleanedlines[$linenumber] =~ s/<(p|span|div|dd|dl|pre)[^>]*>//gis;
              $cleanedlines[$linenumber] =~ s/<\/(p|span|div|dd|dl|pre)[^>]*>//gis;
              $chunk .= $cleanedlines[$linenumber] . "\n";
              $wasadded = q(1);
              ##print "DEBUG: cleaned up tr line: $cleanedlines[$linenumber]\n";
              last;
            }
            ##print "DEBUG: $token->[0]; $token->[1]{'id'};\n";
            if ((      $token->[0] eq 'S'
                    && $token->[2] && $token->[2]{'lang'}
                )
                )
            {
                $file_lang = $token->[2]{'lang'};
                if (lc $file_lang eq q(en-us)) {$file_lang = q(en);}
                if (lc $file_lang eq q(en.us)) {$file_lang = q(en);}
            }

            if ((      $token->[0] eq 'S'
                    && $token->[1] eq 'meta'
                    && $token->[2]{'name'}
                    && $token->[2]{'name'} eq 'generator'
                    && $token->[2]{'content'}
                    && lc( $token->[2]{'content'} ) =~ m/jadey/gis
                )
                )
            {
                $javadoc = q(1);
            }

            if ($token->[1] =~ m/table/isxm) {
              ##$pointer_description = q();
              if ($token->[2]{'title'}) {
                ##print "DEBUG:: : Title: $token->[2]{'title'}\n";
                $token->[2]{'title'} =~ s/^\s+//gis;
                $token->[2]{'title'} =~ s/\s+$//gis;
                $token->[2]{'title'} =~ s/\.$//gis;
                $pointer_description   .= $token->[2]{'title'}.". ";
              }
              if ($token->[2]{'summary'}) {
                ##print "DEBUG:: : Summary: $token->[2]{'summary'}\n";
                $token->[2]{'summary'} =~ s/^\s+//gis;
                $token->[2]{'summary'} =~ s/\s+$//gis;
                $token->[2]{'summary'} =~ s/\.$//gis;
                $pointer_description .= $token->[2]{'summary'}.".";
              }
              ##print "DEBUG:: : pointer_description: $pointer_description\n";
            }

            if ($isPSFT eq q(1) && $token->[1] =~ m/h[1-3]/isxm && $token->[2]{'class'} && $token->[2]{'class'} =~ m/PTPAGELETHEADER/)
            {
                ##print "DEBUG:: : Call beautify at 1\n";
                # head was found
                # 1. check if the previous collection has ID, head and body
                ( $head, $body, $chunkclass, $chunkheadlevel, @allids )
                    = beautify_chunk($chunk);
                if (   length $head < 1
                    || length $body < 1
                    || ( scalar @allids < 1 )
                    || verify_chunk( $head, $body ) == 0 )
                {
                    # continue to add
                    if ( $wasadded ne q(1) ) {
                        $chunk .= $cleanedlines[$linenumber] . "\n";
                        $wasadded = q(1);
                    }
                }
                elsif (length $head > 0
                    && length $body > 0
                    && ( scalar @allids ) > 0 )
                {
                    # chunk formed
                    my $stdocidb  = get_apt_id(@allids);
                    $lastidused = $stdocidb;
                    my $chunkname = $file_name_val . q(-) . $stdocid;
                    $count_chunks++;
                    chunk_manager( $file, $stdocidb,
                        $file_path . q(/) . $chunkname,
                        $chunk, $head, $body, $chunkclass, $chunkheadlevel );
                    $head           = q();
                    $body           = q();
                    $chunkclass     = q();
                    $chunkheadlevel = q();
                    @allids         = ();
                    $chunk          = q();

                    if ( $wasadded ne q(1) ) {
                        $chunk    = $cleanedlines[$linenumber] . "\n";
                        $wasadded = q(1);
                    }
                }
            }
            elsif ($isPSFT ne q(1) && $javadoc ne q(1) && $token->[0] eq 'S'
                && ((   $token->[2]{'class'}
                        && ( any { $_ eq $token->[2]{'class'} } @headclasses )
                    )
                    || ( $token->[1] =~ m/h[1-3]/isxm )
                    || ( ( $token->[1] =~ m/dt/gis ) && $javadoc ne q(1) && $noid ne "1")
                    || ( $token->[1] =~ m/caption/isxm )
                    || ( ($tableprocessing && $token->[1] =~ m/tr/isxm ) && $javadoc ne q(1) && $noid ne "1")
                )
                )
            {

                ##print "DEBUG: Pass breaking $token->[1]\n";
                # head was found
                # 1. check if the previous collection has ID, head and body
                ##print "DEBUG:: : Call beautify at 2\n";
                if (length $chunk > 0) {
                  ( $head, $body, $chunkclass, $chunkheadlevel, @allids )
                    = beautify_chunk($chunk);
                  ##print "DEBUG:: GOT: '$head', '$body'\n";
                  if (   length $head < 1
                    || length $body < 1
                    || ( scalar @allids < 1 )
                    || verify_chunk( $head, $body ) == 0 )
                  {
                    # continue to add
                    if ( $wasadded ne q(1) ) {
                        ##print "DEBUG:: : Added at 1: $cleanedlines[$linenumber]\n";
                        $chunk .= $cleanedlines[$linenumber] . "\n";
                        $wasadded = q(1);
                    }
                  }
                  elsif (length $head > 0
                    && length $body > 0
                    && ( scalar @allids ) > 0 )
                  {
                    # chunk formed
                    my $stdocidb  = get_apt_id(@allids);
                    $lastidused = $stdocidb;
                    my $chunkname = $file_name_val . q(-) . $stdocid;
                    $count_chunks++;
                    chunk_manager( $file, $stdocidb,
                        $file_path . q(/) . $chunkname,
                        $chunk, $head, $body, $chunkclass, $chunkheadlevel );
                    $head           = q();
                    $body           = q();
                    $chunkclass     = q();
                    $chunkheadlevel = q();
                    @allids         = ();
                    $chunk          = q();

                    if ( $wasadded ne q(1) ) {
                        $chunk    = $cleanedlines[$linenumber] . "\n";
                        $wasadded = q(1);
                    }
                  }
                }
            }
            elsif (

                (
                  (
                         (   $token->[0] eq q(S) && $token->[2]{'id'} && length $token->[2]{'id'} > 0 )
                      || (   $token->[0] eq q(S) && $token->[1] eq q(a) && $token->[2]{'name'} && length $token->[2]{'name'} > 0 )
                  )
                  && ! ( $token->[2]{'class'} && any { $_ eq $token->[2]{'class'} } @donotbreakat_class )
                  && ! ( any { $cleanedlines[$linenumber] =~ m/class(\s)*=(\s)*"$_"/ } @donotbreakat_class )
                  ##&& ! ($token->[2]{'id'} && any { $token->[2]{'id'} =~ m/$_/} @donotbreakat_id_regex) 
                  ##&& ! ($token->[2]{'name'} && any { $token->[2]{'name'} =~ m/$_/} @donotbreakat_id_regex) 
                )
                &&
                (      !( $token->[1] eq 'th' )    # do not consider tables
                    && !( $token->[1] eq 'tr' )
                    && !( $token->[1] eq 'thead' )
                    && !( $token->[1] eq 'tbody' )
                    &&  ( $javadoc ne q(1) ) 
                )
                &&
                $isPSFT ne q(1)
                )
            {
                # ##print "DEBUG: Pass third one: $token->[1]; $cleanedlines[$linenumber]\n";
                # this could also mark the beginning
                ##print "DEBUG: Entered ID\n";
                if (   ($token->[2]{'id'} && $token->[2]{'id'} =~ m/BEGIN/isxm)
                    || ($token->[2]{'name'} && $token->[2]{'name'} =~ m/BEGIN/isxm) )
                {
                    $chunk = q();
                }
                if (   ($token->[2]{'id'} && ($token->[2]{'id'} =~ m/sthref(\d)+/gsxm || $token->[2]{'id'} =~ m/^d(\d)+e(\d)+$/gsxm || $token->[2]{'id'} =~ m/i(\d)+/gis || $token->[2]{'id'} =~ m/^[A-Z]{8,}$/ || $token->[2]{'id'} =~ m/GUID-/ || $token->[2]{'id'} =~ m/r[0-9]+c[0-9]+[-_]t[0-9]+/i || $token->[2]{'id'} =~ m/^[0-9]+$/i))
                    || ($token->[2]{'name'} && ($token->[2]{'name'} =~ m/^d(\d)+e(\d)+$/gsxm || $token->[2]{'name'} =~ m/sthref(\d)+/gsxm || $token->[2]{'name'} =~ m/i(\d)+/gis || $token->[2]{'name'} =~ m/[A-Z]{8,}/|| $token->[2]{'name'} =~ m/GUID-/ || $token->[2]{'name'} =~ m/r[0-9]+c[0-9]+[-_]t[0-9]+/i || $token->[2]{'name'} =~ m/^[0-9]+$/i))
                    || ($token->[2]{'class'} && ($token->[2]{'class'} =~ m/^d(\d)+e(\d)+$/gsxm || $token->[2]{'class'} =~ m/notealso(\d)+/gisxm || $token->[2]{'class'} =~ m/seealso/gis || $token->[2]{'class'} =~ m/note/gis))
                )
                {
                    if ( $wasadded ne q(1) ) {
                        ##print "DEBUG:: : Added at 2: $cleanedlines[$linenumber]\n";
                        $chunk .= $cleanedlines[$linenumber] . "\n";
                        $wasadded = q(1);
                    }
                }
                else {

                    $last_id_found = $token->[2]{'id'};
                    if ( $token->[2]{'name'} && length $token->[2]{'name'} > 0
                        && (! $token->[2]{'id'} || length $token->[2]{'id'} < 1) )
                    {
                        $last_id_found = $token->[2]{'name'};
                    }
                    ##print "DEBUG:: : Call beautify at 3\n";
                    ( $head, $body, $chunkclass, $chunkheadlevel, @allids )
                        = beautify_chunk($chunk);

                    if (   length $head < 1
                        || length $body < 1
                        || ( scalar @allids < 1 )
                        || verify_chunk( $head, $body ) == 0 )
                    {
                        # continue to add
                        if ( $wasadded ne q(1) ) {
                            ##print "DEBUG:: : Added at 3: $cleanedlines[$linenumber]\n";
                            $chunk .= $cleanedlines[$linenumber] . "\n";
                            $wasadded = q(1);
                        }
                    }
                    elsif (length $head > 0
                        && length $body > 0
                        && ( scalar @allids ) > 0 )
                    {
                        # chunk formed
                        my $stdocid   = get_apt_id(@allids);
                        $lastidused = $stdocid;
                        my $chunkname = $file_name_val . q(-) . $stdocid;
                        $count_chunks++;

                        chunk_manager(
                            $file,                          $stdocid,
                            $file_path . q(/) . $chunkname, $chunk,
                            $head,                          $body,
                            $chunkclass,                    $chunkheadlevel
                        );
                        $head           = q();
                        $body           = q();
                        $chunk          = q();
                        $chunkclass     = q();
                        $chunkheadlevel = q();
                        @allids         = ();
                        if ( $wasadded ne q(1) ) {
                            $chunk    = $cleanedlines[$linenumber] . "\n";
                            $wasadded = q(1);
                        }
                    }
                }
            }
            else {
                # continue to add lines
                if ( $wasadded ne q(1) ) {
                    ##print "DEBUG:: : Added at 4: $cleanedlines[$linenumber]\n";
                    $chunk .= $cleanedlines[$linenumber] . "\n";
                    $wasadded = q(1);
                }
            }
        }
    }

 # here the holder will have the last ID and its text...so write it as a chunk
    if (scalar @allids < 1) {
        @allids = extractids (\$chunk);
        if (! $lastidused || length ($lastidused) < 1) {
            push @allids, "JUSTANID";
        }
        else {
            push @allids, $lastidused;
        }
    }
    if ( length $chunk > 0 ) {
          ##print "DEBUG: outside beautify\n";
          ( $head, $body, $chunkclass, $chunkheadlevel, @allids )
              = beautify_chunk($chunk);

          if (   length $head > 0
            && length $body > 0
            && ( scalar @allids > 0 ) )
          {
            if (scalar keys %chunk_storage > 0) {
              write_chunk_data();  
              %chunk_storage = ();
              $chunk = q();
            }
            my $stdocid = get_apt_id(@allids);
            if ( length $stdocid < 1 ) {
                $stdocid = $last_id;
            }
            my $chunkname = $file_name_val . q(-) . $stdocid;
            $count_chunks++;
            ##print "DEBUG: outside write_chunk\n";
            write_chunk( $file, $stdocid, $file_path . q(/) . $chunkname,
                $chunk, $head, $body, $chunkclass, $chunkheadlevel );
            $thisfilechunkcount++;
            $chunk = q();
          }
          elsif (defined $chunk_storage{"chunk"}) {
            $chunk = $chunk_storage{"chunk"}.$chunk;
          }
    }

    if ( length $chunk > 0 ) {
          ( $head, $body, $chunkclass, $chunkheadlevel, @allids )
              = beautify_chunk($chunk);

          if (   length $head > 0
            && length $body > 0
            && ( scalar @allids > 0 ) )
          {
            my $stdocid = get_apt_id(@allids);
            if ( length $stdocid < 1 ) {
                $stdocid = $last_id;
            }
            my $chunkname = $file_name_val . q(-) . $stdocid;
            $count_chunks++;
            ##print "DEBUG: write_chunk again outside\n";
            write_chunk( $file, $stdocid, $file_path . q(/) . $chunkname,
                $chunk, $head, $body, $chunkclass, $chunkheadlevel );
            $thisfilechunkcount++;

            reinitialize_chunker();
            $chunk = q();
          }
          else {
            my $idstreamlast = HTML::TokeParser->new( \$chunk )
                or carp "Couldn't parse: $OS_ERROR\n";
            my $alltext = '';
            while ( my $stokenp = $idstreamlast->get_token() ) {
                $alltext
                    .= q( ) . $idstreamlast->get_trimmed_text();
            }
            $alltext =~ s/^( )+//gis;
            $alltext =~ s/( )+$//gis;
            $alltext =~ s/( )+/ /gis;
            my $file_path_to_use = $file;
            $file_path_to_use =~ s/\\/\//gis;
            ##print "DEBUG:: : calling writejsonchunk at 1\n";
            writejsonchunk( "JUSTANID", $chaptertitle, $alltext, $file_path_to_use."-abc", "", $file_path_to_use);
            ##writejsonchunk( $id_val, $cleanhead, $shortbody, $chunkpath, $classtarget, $cpth);
          }
    }

    $chunk = q();
    $lastidused = q();
    reinitialize_chunker();
    # was any chunk written?
    if ($thisfilechunkcount < 1) {
        # get all the text and write to the json
        my $idstreamlast = HTML::TokeParser->new( \$filejoined )
            or carp "Couldn't parse: $OS_ERROR\n";
        my $alltext = '';
        while ( my $stokenp = $idstreamlast->get_token() ) {
            $alltext
                .= q( ) . $idstreamlast->get_trimmed_text();
        }
        $alltext =~ s/^( )+//gis;
        $alltext =~ s/( )+$//gis;
        $alltext =~ s/( )+/ /gis;
        my $file_path_to_use = $file;
        $file_path_to_use =~ s/\\/\//gis;
        ##print "DEBUG:: : calling writejsonchunk at 1\n";
        writejsonchunk( "JUSTANID", $chaptertitle, $alltext, $file_path_to_use."-abc", "", $file_path_to_use);
        ##writejsonchunk( $id_val, $cleanhead, $shortbody, $chunkpath, $classtarget, $cpth);
    }
    $filejoined   = q();
    undef @cleanedlines;
}

# Construct the Summary:
$time = time - $time;
$time = time_format_standard($time);
my $topic_type_summary = q();
foreach my $keys (keys %topic_types_found){
    $topic_type_summary = $topic_type_summary.$keys.q(:).$topic_types_found{$keys}.";";
}
my $summary
    = q(Summary for run on ) . $check_date . "                           \n";
$summary .= "--------------------------------------------\n";
$summary .= q(Total Files Scanned   : )
    . ( ( scalar @dir ) - $ignore_track ) . "\n";
$summary .= q(Total Files Ignored   : ) . $ignore_track . "\n";
$summary .= q(Total mappings        : ) . scalar (keys %index_type_mappings) . "\n";
$summary .= q(Total JSON Chunks     : ) . $summary_count . "\n";
$summary .= q(Topic Types found     : ) . $topic_type_summary . "\n";
$summary .= q(Total time Taken      : ) . $time . "\n";
$summary .= "=========================================================\n";
$summary .= "Errors: \n";

foreach my $el (@errorlines) {
    $summary .= $el . "\n";
}

open my $SUMMARY, '>', $output_folder . q(/log.txt)
    or croak "Cannot open log for writing: $OS_ERROR";
binmode $SUMMARY, ':encoding(UTF-8)';
print {$SUMMARY} $summary . "\n";
close $SUMMARY
    or carp "Can't close summary file: $OS_ERROR";

printf qq[\r$summary\t];

################################################################################

################################################################################
## sub-routines
################################################################################

##############################################################################
# Function: is_html_file
# Parameters:
#
# Description: Tests to see if the file passed is an htm[l] file and checks is it needs to
# be ignored
##############################################################################

sub is_html_file {
    my $filename = shift @_;
    if ( $filename =~ /[.]ht(m|ml)$/ ) {
        return 1;
    }
    return 0;

}

sub reinitialize_chunker {
  delete $chunk_storage{"file"};
  delete $chunk_storage{"stdocid"};
  delete $chunk_storage{"chunk_path"};
  delete $chunk_storage{"chunk"};
  delete $chunk_storage{"head"};
  delete $chunk_storage{"body"};
  delete $chunk_storage{"class"};
  delete $chunk_storage{"headlevel"};
}
##############################################################################
# Function: is_ignored
# Parameters:
#
# Description: Test if a filename is a special one we don't index.
##############################################################################

sub is_ignored {
    my $filename = shift @_;
    return ( $filename =~ /index(.*)[.]ht(m|ml)$/isxm );
}

##############################################################################
# Function: wanted
# Parameters:
#
# Description: Traversal method to get the list of files to be processed
##############################################################################

sub wanted {
    my $temp = $_;
    if (   is_html_file($temp)
        && $temp !~ m/.*\/img_text\/.*/gis
        && $temp !~ m/.*\/images\/([^\/]*)/gis
        && $temp !~ m/.*\/image([^\/]*)\/([^\/]*)/gis
        && $temp !~ m/.*\/dcommon\/.*/gis
        && $temp !~ m/.*\/nav\/.*/gis )
    {

        if ( $temp =~ m/index.html$/gis && checkfilesimilarity($temp)) {
            ## do not process the index.html
            print "Not considering $temp\n";
        }
        else {
          @dir = ( @dir, $temp );
        }
        if ( $temp =~ m/title.htm$/gis ) {
            push @titlefiles, $temp;
        }
    }
    return;
}

##############################################################################
# Function: is_xlink
# Parameters:
#
# Description: Test if an anchor represents an xlink.
##############################################################################

sub is_xlink {
    my $anchor = shift @_;
    return ( $anchor =~ /^[[:upper:]]{5}[\d]{3,5}$/isxm );
}

##############################################################################
# Function: time_format_standard
# Parameters:
#
# Description: Converts seconds to format HH::MM::SS
##############################################################################

sub time_format_standard {
    my $time_passed  = shift;
    my $seconds_here = $time_passed % $SHORTCUT_CHAR_LENGTH_SIXTY;

    my $minutes_here = int( $time_passed / $SHORTCUT_CHAR_LENGTH_SIXTY );
    my $hours_here   = int( $minutes_here / $SHORTCUT_CHAR_LENGTH_SIXTY );
    $minutes_here
        = $minutes_here - ( $hours_here * $SHORTCUT_CHAR_LENGTH_SIXTY );

    if ( $hours_here < $SHORTCUT_CHAR_LENGTH_TEN ) {
        $hours_here = q(0) . $hours_here;
    }
    if ( $minutes_here < $SHORTCUT_CHAR_LENGTH_TEN ) {
        $minutes_here = q(0) . $minutes_here;
    }
    if ( $seconds_here < $SHORTCUT_CHAR_LENGTH_TEN ) {
        $seconds_here = q(0) . $seconds_here;
    }

    my $ret_val = $hours_here . q(:) . $minutes_here . q(:) . $seconds_here;
    return $ret_val;
}

sub chunk_manager {

  my $chunkfile           = shift;
  my $chunk_idv           = shift;
  my $chunk_complete_path = shift;
  my $chunk_lines         = shift;
  my $chunk_head          = shift;
  my $chunk_body_all      = shift;
  my $chunk_class_val     = shift;
  my $chunk_headlevel_val = shift;
  ##print "DEBUG:: : writing at 2\n";
  ##print "DEBUG:: : writing at 2H: $chunk_head\n";
  ##print "DEBUG:: : writing at 2B: $chunk_body_all\n";
  write_chunk_data ();
  ##print "DEBUG:: : Assigning values to chunker\n";
  $chunk_storage{"file"} = $chunkfile;
  $chunk_storage{"stdocid"} = $chunk_idv;
  $chunk_storage{"chunk_path"} = $chunk_complete_path;
  $chunk_storage{"chunk"} = $chunk_lines;
  $chunk_storage{"head"} = $chunk_head;
  $chunk_storage{"body"} = $chunk_body_all;
  $chunk_storage{"class"} = $chunk_class_val;
  $chunk_storage{"headlevel"} = $chunk_headlevel_val;
  return;
}

sub write_chunk_data {
  if (scalar keys %chunk_storage > 0) {
    ##print "DEBUG:: : Writing chunk now: \n\nHEAD:".$chunk_storage{"head"}."\n\nBODY:".$chunk_storage{"body"}."\n\n";
    ## write it to the json
    write_chunk( $chunk_storage{"file"}, $chunk_storage{"stdocid"},
        $chunk_storage{"chunk_path"},
        $chunk_storage{"chunk"}, $chunk_storage{"head"}, $chunk_storage{"body"}, $chunk_storage{"class"}, $chunk_storage{"headlevel"} );
    reinitialize_chunker();
  }
  return;
}

sub append_chunk_lines {
  my $additional_chunk = shift;
  if (scalar keys %chunk_storage > 0 && length $additional_chunk > 0) {
    ## append the chunk
    $chunk_storage{"chunk"} .= $additional_chunk;
  }
  return;
}

##############################################################################
# Function: write_chunk
# Parameters:
#
# Description: write to a chunk file
##############################################################################

sub write_chunk {
    my $file_being_studied = shift;
    my $id_val             = shift;
    my $chunkpath          = shift;
    my $chunkcontent       = shift;
    my $headpart           = shift;
    my $bodypart           = shift;
    my $original_body      = $bodypart;
    my $chunkcl = shift;
    my $chunkhl = shift;
    $lastchunkwritten = $chunkpath;
    if ( length $id_val < 1 || length $headpart < 1 || length $bodypart < 1 )
    {
        ##print "DEBUG:: : Returned at 3: $id_val : $headpart : $bodypart\n";
        return;
    }
    my $newidval = $id_val;
    $newidval =~ s/\r//gis;
    $newidval =~ s/\n//gis;
    if ( $newidval ne $id_val ) {
        ##print "DEBUG:: : Returned at 4\n";
        return;
    }

    my $plainhead = removehtmlmarkupbody($headpart);
    $bodypart =~ s/^\Q$plainhead\E(\s)*//;
    ##$bodypart =~ s/^([\s\d.]+)//isxm;

    #$original_body =~ s/^([\s\d.]+)//i;
    #$original_body =~ s/^\Q$plainhead\E(\s)*//;

    if ( length $bodypart < 1 ) {
        $bodypart = $original_body;
    }

    $bodypart =~ s/</&lt;/gis;
    $bodypart =~ s/>/&gt;/gis;

    if ( $headpart =~ m/<head><\/head>/isxm ) {
        $headpart = q();
        my @pextractedwords = split / /, $bodypart;
        foreach my $wrds (@pextractedwords) {
            $headpart .= $wrds . q( );
            if ( length $headpart > $SHORTCUT_CHAR_LENGTH_NINENINE ) {
                last;
            }
        }
        $headpart = q(<head>) . $headpart . q(</head>);
    }
    my $cleanedcontent = $headpart."\n".$bodypart;
    my $cleanhead = removehtmlmarkup($headpart);
    my $shortbody = removehtmlmarkupbodyall($original_body);
    ##print "DEBUG:: : Now writing chunk: $id_val, $cleanhead, $shortbody, $chunkpath, $classtarget, $cpth\n";
    ##print "DEBUG:: : calling writejsonchunk at 2\n";
    writejsonchunk( $id_val, $cleanhead, $shortbody, $chunkpath, $chunkcl, $chunkpath);

    return;
}

##############################################################################
# Function: beautify_chunk
# Parameters:
#
# Description: scans the chunk and tries to filter it.
# to do: remove the a id tags from the filtered head .
# These ids should also be attached to the @allids
# to do: get the head from the element A title
##############################################################################

sub beautify_chunk {
    my $text_to_scan = shift;
    trim (\$text_to_scan);
    my $text_backup  = $text_to_scan;
    $text_to_scan =~ s/\r//gis;
    $text_to_scan =~ s/\n//gis;
    ####print "DEBUG: : Here beautify_chunk -> $text_to_scan\n";
    my $was_head_found    = q();
    my $was_section_found = q();
    my $relevant_head     = q();
    my $relevanttext      = q();
    my $text_before_head  = q();
    my $id_lines          = q();
    my @extract_ids       = ();
    my $class             = q();
    my $headlevel         = q();

    my $wasrelevancefound = q();

    if (   $text_to_scan =~ m/<h[1-3]([^>]*)>/gis
        || $text_to_scan =~ m/<\/h[1-3]>/gis )
    {
        $wasrelevancefound = q(1);
        ##print "DEBUG:: : RELEVANCE 1\n";
    }
    elsif (   $text_to_scan =~ m/<dt(\s)*([^>]*)>/gis
           && $text_to_scan =~ m/<\/dt>/gis
          )
    {
        $wasrelevancefound = q(1);
        ##print "DEBUG:: : RELEVANCE 2\n";
    }
    elsif ($text_to_scan =~ m/<tr([^>]*)>/gis
        && $text_to_scan =~ m/<\/tr>/gis )
    {
        $wasrelevancefound = q(1);
    }
    else {
        foreach my $searchclass (@headclasses) {
            if ( $text_to_scan =~ m/"$searchclass"/gis ) {
                $wasrelevancefound = q(1);
                $class             = $searchclass;
            }
        }
    }
    ##print "DEBUG:: : RELEVANCE VAL: $wasrelevancefound\n";

    if (( $wasrelevancefound eq q(0) )
        && (   $text_to_scan =~ m/<tr([^>]+)>/gis
            && $text_to_scan !~ m/<\/tr>/gis )
        )
    {
        return ( $relevant_head, $relevanttext, $class, $headlevel,
            @extract_ids );
    }
    if (( $wasrelevancefound eq q(0) )
        && (   $text_to_scan =~ m/<\/p>/gis
            || $text_to_scan =~ m/<p ([^>]+)>/gis )
        )
    {
        $wasrelevancefound = q(1);

        # special case when the id was found and the head is not there but <p>
        # available.
        # make the first 100 characters as head.
        my $idstreamp = HTML::TokeParser->new( \$text_backup )
            or carp "Couldn't parse: $OS_ERROR\n";
        while ( my $idtokenp = $idstreamp->get_token() ) {
            if (   ( $idtokenp->[0] eq 'S' && $idtokenp->[1] eq 'a' )
                || ( length $idtokenp->[2]{'id'} > 0 ) )
            {
                my $secidp   = $idtokenp->[2]{'id'};
                my $secnamep = $idtokenp->[2]{'name'};

                if ( length $secnamep > 0 ) {
                    $secidp = $secnamep;
                }
                if ( length $secidp > 0 ) {
                    push @extract_ids, $secidp;
                }
            }
        }
        if ( scalar @extract_ids < 1 ) {
            return ( $relevant_head, $relevanttext, $class,
                $headlevel, @extract_ids );
        }
        my $extractedplaintextp = q();
        if ( $text_backup =~ m/<title>(.*)<\/title>/isxm ) {
            $relevant_head = $1;
            if ( length $relevant_head > 0 ) {
                $relevant_head = q(<head>) . $relevant_head . q(</head>);
            }
        }
        my $sectionstreamp = HTML::TokeParser->new( \$text_backup )
            or carp "Couldn't parse: $OS_ERROR";
        while ( my $stokenp = $sectionstreamp->get_token() ) {
            $extractedplaintextp
                .= q( ) . $sectionstreamp->get_trimmed_text();
        }

        # get the first
        if ( length $extractedplaintextp <= $HUNDRED ) {
            $relevant_head = q(<head>) . $extractedplaintextp . q(</head>);
            $relevanttext  = $extractedplaintextp;
            $headlevel     = q();
        }
        else {
            $relevant_head = q();
            $relevanttext  = $extractedplaintextp;
            my @extractedwords = split / /, $extractedplaintextp;
            foreach my $wrds (@extractedwords) {
                $relevant_head .= $wrds . q( );
                if ( length $relevant_head > $SHORTCUT_CHAR_LENGTH_NINENINE )
                {
                    last;
                }
            }
            $relevant_head =~ s/^(\s)+//gis;
            $relevant_head =~ s/(\s)+$//gis;
            $relevanttext =~ s/^(\s)+//gis;
            $relevanttext =~ s/(\s)+$//gis;

            if ( length $relevant_head > 0 ) {
                $relevant_head = q(<head>) . $relevant_head . q(</head>);
            }
        }
        return ( $relevant_head, $relevanttext, $class, $headlevel,
            @extract_ids );
    }
    ##print "DEBUG:: : RELEVANCE VAL N: $wasrelevancefound\n";

    @extract_ids = ();

    if ( $wasrelevancefound eq q(0) ) {
        return ( $relevant_head, $relevanttext, $class, $headlevel,
            @extract_ids );
    }

    if (   $text_to_scan =~ m/<\/h[1-3]>/is
        && $text_to_scan !~ m/<h[1-3]>.*<\/h[1-3]>/is )
    {
        if ( $text_to_scan =~ m/<\/h([1-3])>/is ) {
            $text_to_scan = q(<h) . $1 . q(>) . $text_to_scan;
        }
    }
    ##if ( $text_to_scan =~ m/(<h[1-3]>(.*)<\/h[1-3]>)(.*)(<h[1-3]>)(.*)/gis )
    ##{
    ##    $text_to_scan = $1 . $3;
    ##}

    my $idstream = HTML::TokeParser->new( \$text_backup )
        or carp "Couldn't parse: $OS_ERROR";
    while ( my $idtoken = $idstream->get_token() ) {
        if (   ( $idtoken->[0] eq 'S' && $idtoken->[1] eq 'a' )
            || ( $idtoken->[2]{'id'} && length $idtoken->[2]{'id'} > 0 ) )
        {
            my $secid   = $idtoken->[2]{'id'};
            my $secname = $idtoken->[2]{'name'};

            if ( $secname && length $secname > 0 ) {
                $secid = $secname;
            }
            if ( $secid && length $secid > 0 ) {
                push @extract_ids, $secid;
            }
        }
        if (   $idtoken
            && $idtoken->[2]{'class'}
            && length $idtoken->[2]{'class'} > 0 )
        {
            my $sectval = $idtoken->[2]{'class'};
        }
    }
    if ( scalar @extract_ids < 1 ) {
        return ( $relevant_head, $relevanttext, $class, $headlevel,
            @extract_ids );
    }

    if ( $text_to_scan =~ m/(.*?)(<h[1-3])(.*)/is ) {
        ##print "DEBUG:: : H clause\n";
        $text_before_head = $1;
        my $headtag = $2;
        $headlevel = $headtag;
        $headlevel =~ s/<h//gis;
        my $headclose = $headtag;
        $headclose =~ s/\</<\//gis;

        # extract the head
        $id_lines = $text_before_head;
        $text_to_scan =~ s/(.*)$headtag//is;

        # from the idLines extract all the IDs
        # done.
        # remove till the closing h
        my $indexresult = index $text_to_scan, '>';

        # check for classes
        $class = substr $text_to_scan, 0,
            $indexresult;    # might be like class=""
        $class =~ s/^\s//gis;
        $class =~ s/\s$//gis;

        if ( $class =~ m/class(\s)*=(\s)*(")*([^"]+)(")*/gis ) {
            $class = $4;
            $class =~ s/\"//gis;
            $class =~ s/^\s//gis;
            $class =~ s/\s$//gis;
        }

        $text_to_scan = substr $text_to_scan, $indexresult + 1;
        if ( $text_to_scan =~ m/(.*)$headclose>(.*)/is ) {
            $relevant_head = $1;
            $relevanttext  = $2;
            $relevant_head =~ s/^(\s)+//gis;
            $relevant_head =~ s/(\s)+$//gis;
            ####print "DEBUG:: : Head: $relevant_head\n";
            ####print "DEBUG:: : TEST: $relevanttext\n";
            if ( length $relevant_head > 0 ) {
                $relevant_head  = q(<head>) . $relevant_head . q(</head>);
                $was_head_found = q(1);

                # now streamify to get the text out of section
                my $extractedplaintext = q();
                my $sectionstream = HTML::TokeParser->new( \$text_backup )
                    or carp "Couldn't parse: $OS_ERROR";
                while ( my $stoken = $sectionstream->get_token() ) {
                    if ( ( $stoken->[0] eq 'S' && $stoken->[1] eq 'img' ) ) {
                        ##$extractedplaintext .= $stoken->[2]{'alt'};
                    }
                    elsif ( ( $stoken->[0] eq 'S' && $stoken->[1] eq 'pre' ) )
                    {
                        $extractedplaintext
                            .= $stoken->[$SHORTCUT_CHAR_LENGTH_FOUR]
                            . $sectionstream->get_trimmed_text('/pre')
                            . q(</pre>);
                    }
                    else {
                        $extractedplaintext
                            .= q( ) . $sectionstream->get_trimmed_text();
                    }
                }
                if ( length $extractedplaintext > 0 ) {
                    $relevanttext = $extractedplaintext;
                    $relevanttext =~ s/(\s)+/ /gis;
                    $relevanttext =~ s/^\s//gis;
                    $relevanttext =~ s/\s$//gis;
                    $was_section_found = q(1);
                }
            }
        }
    }
    if (   $was_head_found eq q(1)
        && $was_section_found eq q(1)
        && ( scalar @extract_ids > 0 ) )
    {
        my $headstream = HTML::TokeParser->new( \$relevant_head )
            or carp "Couldn't parse: $OS_ERROR";
        while ( my $htoken = $headstream->get_token() ) {
            if (( $htoken->[0] eq 'S' || $htoken->[0] eq 'E' )
                && (   $htoken->[1] eq 'a'
                    || $htoken->[1] eq 'dt'
                    || $htoken->[1] eq 'p'
                    || $htoken->[1] eq 'dd'
                    || $htoken->[1] eq 'th'
                    || $htoken->[1] eq 'td'
                    || $htoken->[1] eq 'tr' )
                )
            {
                if ( $htoken->[$SHORTCUT_CHAR_LENGTH_FOUR] ) {
                    my $atag = $htoken->[$SHORTCUT_CHAR_LENGTH_FOUR];
                    $relevant_head =~ s/\Q$atag\E//gis;
                }
            }
        }
        $relevant_head = removeunclosedtags($relevant_head);
        $relevant_head =~ s/\r//gis;
        $relevant_head =~ s/\n//gis;
        ####print "DEBUG:: : relevant_head_finally: $relevant_head\n";
        ####print "DEBUG:: : relevant_text_finally: $relevanttext\n";
        return ( $relevant_head, $relevanttext, $class, $headlevel,
            @extract_ids );
    }
    ##print "DEBUG:: : Reached after H\n";
    #############################################################################
    # if I reach here, I need to see for other ways
    # of grabbing the head and section.
    # caption, dt, th
    #############################################################################
    my @boldheads = ( 'caption', 'dt' );
    $text_to_scan      = $text_backup;
    $was_head_found    = q();
    $relevant_head     = q();
    $relevanttext      = q();
    $was_section_found = q();

    if (   $text_to_scan =~ m/<\/dt>/gis
        && $text_to_scan !~ m/<dt([^>]*)>.*<\/dt>/gis )
    {
        $text_to_scan = q(<dt>) . $text_to_scan;
    }
    if (   $text_to_scan =~ m/<\/tr>/gis
        && $text_to_scan !~ m/<tr([^>]*)>.*<\/tr>/gis )
    {
        $text_to_scan = q(<tr>) . $text_to_scan;
    }

    if ( $text_to_scan =~ m/(<dt>(.*)<\/dt>)(.*)(<dt>)(.*)/gis ) {
        $text_to_scan = $1 . $3;
    }
    if ( $text_to_scan =~ m/(<tr>(.*)<\/tr>)(.*)(<tr>)(.*)/gis ) {
        ##$text_to_scan = $1 . $3;
    }

    # create the token stream

    my $idstreamm = HTML::TokeParser->new( \$text_to_scan )
        or carp "Couldn't parse: $OS_ERROR";
    while ( my $idtoken = $idstreamm->get_token() ) {
        if ($idtoken->[0] eq 'S'
            && (   $idtoken->[1] eq 'caption'
                || $idtoken->[1] eq 'dt'
                || $idtoken->[1] eq 'tr'
                || ($idtoken->[2]{'class'} && any { $_ eq $idtoken->[2]{'class'} } @tabletitleclass)
                )
            )
        {
            my $headtoken = $idtoken->[$SHORTCUT_CHAR_LENGTH_FOUR];
            my $headtag   = $idtoken->[1];
            ##print "DEBUG:: : Pass i am in : $headtoken; $headtag\n";
            ##print "DEBUG:: : text_to_scan: $text_to_scan\n\n\n\n";

            if ( $text_to_scan =~ m/(.*)$headtoken(.*)/is ) {
                my $indexresult = index $text_to_scan, $headtoken;
                $id_lines = substr $text_to_scan, 0, $indexresult;
                $relevant_head = substr $text_to_scan,
                    $indexresult + ( length $headtoken ),
                    length $text_to_scan;

                $indexresult = index lc ($relevant_head), '</' . $headtag . '>';
                my $rhead = substr $relevant_head, 0, $indexresult;
                if ($indexresult >= 0){
                    $relevanttext = substr $relevant_head,
                        $indexresult
                        + ( length ($headtag) + $SHORTCUT_CHAR_LENGTH ),
                        length ($relevant_head);
                }
                $relevant_head = $rhead;
                $relevant_head =~ s/^(\s)+//gis;
                $relevant_head =~ s/(\s)+$//gis;
                if ( length $relevant_head > 0 ) {
                    $relevant_head  = q(<head>) . $relevant_head . q(</head>);
                    $was_head_found = q(1);
                    if ( length $relevanttext > 0 ) {
                        my $extractedplaintext = q();
                        my $sectionstream
                            = HTML::TokeParser->new( \$text_backup )
                            or carp "Couldn't parse: $OS_ERROR";
                        while ( my $stoken = $sectionstream->get_token() ) {
                            if ((      $stoken->[0] eq 'S'
                                    && $stoken->[1] eq 'img'
                                )
                                )
                            {
                                ##$extractedplaintext .= $stoken->[2]{'alt'};
                            }
                            elsif (
                                (      $stoken->[0] eq 'S'
                                    && $stoken->[1] eq 'pre'
                                )
                                )
                            {
                                $extractedplaintext
                                    .= $stoken->[$SHORTCUT_CHAR_LENGTH_FOUR]
                                    . $sectionstream->get_trimmed_text('/pre')
                                    . q(</pre>);
                            }
                            else {
                                $extractedplaintext .= q( )
                                    . $sectionstream->get_trimmed_text();
                            }
                        }
                        if ( length $extractedplaintext > 0 ) {
                            $relevanttext = $extractedplaintext;
                            $relevanttext =~ s/(\s)+/ /gis;
                            $relevanttext =~ s/^\s//gis;
                            $relevanttext =~ s/\s$//gis;
                            $was_section_found = q(1);
                        }
                    }
                }
            }
        }
        if ( $was_head_found eq q(1) && $was_section_found eq q(1) ) {
            last;
        }
    }
    ##print "DEBUG:: : Pass IDENTIFIVXATION: $was_head_found ($relevant_head):$was_section_found:".(scalar @extract_ids)."\n";
    if (   $was_head_found eq q(1)
        && $was_section_found eq q(1)
        && ( scalar @extract_ids > 0 ) )
    {
        my $headstream = HTML::TokeParser->new( \$relevant_head )
            or carp "Couldn't parse: $OS_ERROR";
        while ( my $htoken = $headstream->get_token() ) {
            if (( $htoken->[0] eq 'S' || $htoken->[0] eq 'E' )
                && (   $htoken->[1] eq 'a'
                    || $htoken->[1] eq 'dt'
                    || $htoken->[1] eq 'p'
                    || $htoken->[1] eq 'dd'
                    || $htoken->[1] eq 'th'
                    || $htoken->[1] eq 'td'
                    || $htoken->[1] eq 'tr' )
                )
            {
                my $atag = $htoken->[$SHORTCUT_CHAR_LENGTH_FOUR];
                if ($atag) {$relevant_head =~ s/\Q$atag\E//gis;}
            }
        }
        $relevant_head = removeunclosedtags($relevant_head);
        $relevant_head =~ s/\r//gis;
        $relevant_head =~ s/\n//gis;
        return ( $relevant_head, $relevanttext, $class, $headlevel,
            @extract_ids );
    }

    #############################################################################
    # if I reach here, I need to see for other ways
    # of grabbing the head and section
    #############################################################################
    $text_to_scan      = $text_backup;
    $was_head_found    = q();
    $relevant_head     = q();
    $relevanttext      = q();
    $was_section_found = q();

    # create the token stream
    my $idstreamn = HTML::TokeParser->new( \$text_to_scan )
        or carp "Couldn't parse: $OS_ERROR";
    while ( my $idtoken = $idstreamn->get_token() ) {

        #if(($idtoken->[0] eq 'S' && $idtoken->[1] eq 'p' )
        if ( ( $idtoken->[0] eq 'S' ) ) {
            if ( $idtoken->[2]{'class'}
                && any { $_ eq $idtoken->[2]{'class'} } @headclasses )
            {
                $class = $idtoken->[2]{'class'};
                my $headtoken        = $idtoken->[$SHORTCUT_CHAR_LENGTH_FOUR];
                my $tagbeinganalysed = $idtoken->[1];
                if ( $text_to_scan =~ m/.*$headtoken.*/ ) {
                    my $indexresult = index $text_to_scan, $headtoken;
                    $id_lines = substr $text_backup, 0, $indexresult;
                    $relevant_head = substr $text_backup,
                        $indexresult + ( length $headtoken ),
                        length $text_backup;
                    #$id_lines = $1;
                    #$relevant_head = $2;

                    $indexresult = index $relevant_head,
                        '</' . $tagbeinganalysed . '>';
                    my $rhead = substr $relevant_head, 0, $indexresult;
                    if ($indexresult > 0) {
                        $relevanttext = substr $relevant_head, ($indexresult + length ($tagbeinganalysed) + $SHORTCUT_CHAR_LENGTH), length $relevant_head;
                    }
                    $relevant_head = $rhead;
                    $relevant_head =~ s/^(\s)+//gis;
                    $relevant_head =~ s/(\s)+$//gis;
                    if ( length $relevant_head > 0 ) {
                        $relevant_head
                            = q(<head>) . $relevant_head . q(</head>);
                        $was_head_found = q(1);
                        if ( length $relevanttext > 0 ) {
                            my $extractedplaintext = q();
                            my $sectionstream
                                = HTML::TokeParser->new( \$text_backup )
                                or carp "Couldn't parse: $OS_ERROR";
                            while ( my $stoken = $sectionstream->get_token() )
                            {
                                if ((      $stoken->[0] eq 'S'
                                        && $stoken->[1] eq 'img'
                                    )
                                    )
                                {
                                    ## $extractedplaintext .= $stoken->[2]{'alt'};
                                }
                                elsif (
                                    (      $stoken->[0] eq 'S'
                                        && $stoken->[1] eq 'pre'
                                    )
                                    )
                                {
                                    $extractedplaintext
                                        .= $stoken
                                        ->[$SHORTCUT_CHAR_LENGTH_FOUR]
                                        . $sectionstream->get_trimmed_text(
                                        '/pre')
                                        . q(</pre>);
                                }
                                else {
                                    $extractedplaintext .= q( )
                                        . $sectionstream->get_trimmed_text();
                                }
                            }
                            if ( length $extractedplaintext > 0 ) {
                                $relevanttext = $extractedplaintext;
                                $relevanttext =~ s/(\s)+/ /gis;
                                $relevanttext =~ s/^\s//gis;
                                $relevanttext =~ s/\s$//gis;
                                $was_section_found = q(1);
                            }
                        }
                    }

                }
            }
        }

        if ( $was_head_found eq q(1) && $was_section_found eq q(1) ) {
            last;
        }
    }

    if (   $was_head_found eq q(1)
        && $was_section_found eq q(1)
        && ( scalar @extract_ids > 0 ) )
    {
        my $headstream = HTML::TokeParser->new( \$relevant_head )
            or carp "Couldn't parse: $OS_ERROR";
        while ( my $htoken = $headstream->get_token() ) {
            if (( $htoken->[0] eq 'S' || $htoken->[0] eq 'E' )
                && (   $htoken->[1] eq 'a'
                    || $htoken->[1] eq 'dt'
                    || $htoken->[1] eq 'p'
                    || $htoken->[1] eq 'dd'
                    || $htoken->[1] eq 'th'
                    || $htoken->[1] eq 'td'
                    || $htoken->[1] eq 'tr' )
                )
            {
                my $atag = $htoken->[$SHORTCUT_CHAR_LENGTH_FOUR];
                if ($atag) {
                    $relevant_head =~ s/\Q$atag\E//gis;
                }
            }
        }
        $relevant_head = removeunclosedtags($relevant_head);
        $relevant_head =~ s/\r//gis;
        $relevant_head =~ s/\n//gis;
        return ( $relevant_head, $relevanttext, $class, $headlevel,
            @extract_ids );
    }

    #############################################################################
    # if I reach here, I need to see for other ways
    # of grabbing the head and section.
    # a title
    #############################################################################
    $text_to_scan      = $text_backup;
    $was_head_found    = q();
    $relevant_head     = q();
    $relevanttext      = q();
    $was_section_found = q();

    # create the token stream
    my $idstreamg = HTML::TokeParser->new( \$text_to_scan )
        or carp "Couldn't parse: $OS_ERROR";
    while ( my $idtoken = $idstreamg->get_token() ) {
        if ($idtoken->[0] eq 'S'
            && (   $idtoken->[1] eq 'a'
                && $idtoken->[2]{'title'}
                && length $idtoken->[2]{'title'} > 0 )
            )
        {
            my $headtoken = $idtoken->[$SHORTCUT_CHAR_LENGTH_FOUR];
            my $headtag   = $idtoken->[1];
            if ( $text_to_scan =~ m/(.*)\Q$headtoken\E(.*)/gis ) {

                $id_lines      = $1 . $headtoken;
                $relevanttext  = $2;
                $relevant_head = $idtoken->[2]{'title'};
                $relevant_head =~ s/^(\s)+//gis;
                $relevant_head =~ s/(\s)+$//gis;

                if ( length $relevant_head > 0 ) {
                    $relevant_head  = q(<head>) . $relevant_head . q(</head>);
                    $was_head_found = q(1);
                    if ( length $relevanttext > 0 ) {
                        my $extractedplaintext = q();
                        my $sectionstream
                            = HTML::TokeParser->new( \$text_backup )
                            or carp "Couldn't parse: $OS_ERROR";
                        while ( my $stoken = $sectionstream->get_token() ) {
                            if ((      $stoken->[0] eq 'S'
                                    && $stoken->[1] eq 'img'
                                )
                                )
                            {
                                ##$extractedplaintext .= $stoken->[2]{'alt'};
                            }
                            elsif (
                                (      $stoken->[0] eq 'S'
                                    && $stoken->[1] eq 'pre'
                                )
                                )
                            {
                                $extractedplaintext
                                    .= $stoken->[$SHORTCUT_CHAR_LENGTH_FOUR]
                                    . $sectionstream->get_trimmed_text('/pre')
                                    . q(</pre>);
                            }
                            else {
                                $extractedplaintext .= q( )
                                    . $sectionstream->get_trimmed_text();
                            }
                        }
                        if ( length $extractedplaintext > 0 ) {
                            $relevanttext = $extractedplaintext;
                            $relevanttext =~ s/(\s)+/ /gis;
                            $relevanttext =~ s/^\s//gis;
                            $relevanttext =~ s/\s$//gis;
                            $was_section_found = q(1);
                        }
                    }
                }
            }
        }
        if ( $was_head_found eq q(1) && $was_section_found eq q(1) ) {
            last;
        }
    }

    if (   $was_head_found eq q(1)
        && $was_section_found eq q(1)
        && ( scalar @extract_ids > 0 ) )
    {
        my $headstream = HTML::TokeParser->new( \$relevant_head )
            or carp "Couldn't parse: $OS_ERROR";
        while ( my $htoken = $headstream->get_token() ) {
            if (( $htoken->[0] eq 'S' || $htoken->[0] eq 'E' )
                && (   $htoken->[1] eq 'a'
                    || $htoken->[1] eq 'p'
                    || $htoken->[1] eq 'dt'
                    || $htoken->[1] eq 'dd'
                    || $htoken->[1] eq 'th'
                    || $htoken->[1] eq 'td'
                    || $htoken->[1] eq 'tr' )
                )
            {
                my $atag = $htoken->[$SHORTCUT_CHAR_LENGTH_FOUR];
                $relevant_head =~ s/\Q$atag\E//gis;
            }
        }
        $relevant_head = removeunclosedtags($relevant_head);
        $relevant_head =~ s/\r//gis;
        $relevant_head =~ s/\n//gis;
        return ( $relevant_head, $relevanttext, $class, $headlevel,
            @extract_ids );
    }
}

##############################################################################
# Function: get_apt_id
# Parameters:
#
# Description: Determines the best ID to use for chunk name
##############################################################################

sub get_apt_id {
    my @idlist = @_;
    my $testid = q();
    foreach my $inid (@idlist) {
        if ( is_xlink($inid) ) {
            $testid = $inid;
            last;
        }
    }
    if ( length $testid < 1 ) {
        foreach my $inid (@idlist) {
            if ( $inid =~ m/([[:upper:]])+/gsxm ) {
                $testid = $inid;
                last;
            }
        }
        if ( length $testid < 1 ) {
            $testid = $idlist[0];
            ##$testid = $idlist[ scalar @idlist - 1 ];
        }
    }
    return $testid;
}


##############################################################################
# Function: arrange
# Parameters:
#
# Description: Arranges the HTML before the processing starts
# so that all the relevant lines are on one line
##############################################################################

sub arrange {
    my $unformattedlines = shift;
    my $whatfile         = shift;
    $unformattedlines =~ s/\r//gis;

    # get the chapter title
    my $idstreamv = HTML::TokeParser->new( \$unformattedlines )
        or carp "Couldn't parse: $OS_ERROR";
    while ( my $tokenh = $idstreamv->get_token() ) {

        if ( ( $tokenh->[0] eq 'S' ) && ( $tokenh->[1] =~ m/title/isxm ) ) {
            $chaptertitle = $idstreamv->get_trimmed_text('/title');
            last;
        }
        if ( ( $tokenh->[0] eq 'S' ) && ( $tokenh->[1] =~ m/h1/isxm ) ) {
            $chaptertitle = $idstreamv->get_trimmed_text('/h1');
            last;
        }
    }

    # if the title.htm was there, then its title is the book title
    if ( $whatfile =~ m/title.htm$/gis && length $chaptertitle > 0 ) {
        my $testpn = &extractpartnumber($whatfile);
        if ( length $testpn > 0 ) {
            if ( !exists $booktitle{$testpn} ) {
                $booktitle{$testpn} = $chaptertitle;
            }
        }
    }

    $unformattedlines =~ s/<head>(.*)<\/head>//gis;
    # GLOBALLY REPLACE STARTING TAG WITH A NEW LINE
    my $formattedfile = 0;    
    if ( any { $unformattedlines =~ m/$_/gisxm } @donotbreakat_class ) {
      $formattedfile = 1;  
    }
    if ( $formattedfile != 1 && any { $unformattedlines =~ m/$_/gisxm } @headclasses ) {
      $formattedfile = 1;
    }
    if ( $formattedfile != 1 && $unformattedlines =~ m/id(\s)*=(\s)*"GUID-/gisxm) {
      $formattedfile = 1;
    }
    if ($formattedfile != 1) {
      $unformattedlines =~ s/(<[[:alpha:]])/\n$1/gis;
      # bring all dt and dd in one line
      #pos( $unformattedlines ) = 0;
      #print "Start\n";
      if ($unformattedlines =~ m/<(dl|tr)([^>]*)>/isxm) {
        if ($javadoc ne q(1) && $ignoretableprocessing ne q(1)) {
          my $tempbuffer = $unformattedlines; 
          while ($unformattedlines =~ m/(<dl([^>]*)>(.*?)<\/dl>)/gisxm) {
            my $exact = $1;
            my $newone = $exact;
            $newone =~ s/\r//gis;
            $newone =~ s/\n//gis;
            $newone =~ s/(<dt)/\n$1/gis;
            $newone =~ s/(<dl)/\n$1/gis;
            $newone =~ s/(<\/dl)/\n$1/gis;
            $tempbuffer =~ s/\Q$exact\E/$newone/gis;
          }
          $unformattedlines = $tempbuffer;
          undef $tempbuffer;
        }
      }
      $unformattedlines =~ s/\r//gis;

      if ($javadoc ne q(1) && $whatfile !~ m/index.ht(m|ml)/ && $ignoretableprocessing ne q(1)) {
        my $tempbuffer = $unformattedlines; 
        while ($unformattedlines =~ m/(<tr[^>]*>(.*?)<\/tr>)/gisxm) {
          my $exact = $1;
          my $newone = $exact;
          $newone =~ s/\r//gis;
          $newone =~ s/\n//gis;
          $tempbuffer =~ s/\Q$exact\E/$newone/gis;

        }
        $unformattedlines = $tempbuffer;
        undef $tempbuffer;
      }
    }

    my @cleanedlinestemp = split /\n/, $unformattedlines;
    undef $idstreamv;
    undef $unformattedlines;
    undef @cleanedlines;
    foreach (@cleanedlinestemp) {
        my $cl = $_;
        $cl =~ s/\n/ /gis;
        if ( length $cl > 0 ) {
            push @cleanedlines, $cl;
        }
    }
    undef @cleanedlinestemp;
}

##############################################################################
# Function: removeunclosedtags
# Parameters:
#
# Description:Rremove unclosed HTML tags
##############################################################################

sub removeunclosedtags {
    my $dirtytext = shift;
    my $idstreamb = HTML::TokeParser->new( \$dirtytext )
        or carp "Couldn't parse: $OS_ERROR";
    while ( my $dtoken = $idstreamb->get_token() ) {
        if ( $dtoken->[0] eq 'S' ) {
            my $atag      = $dtoken->[$SHORTCUT_CHAR_LENGTH_FOUR];
            my $close_tag = q(</) . $dtoken->[1] . q(>);
            if (   $dirtytext =~ m/\Q$atag\E/isxm
                && $dirtytext !~ m/\Q$close_tag\E/isxm )
            {
                $dirtytext =~ s/\Q$atag\E//isxm;
            }
        }
        elsif ( $dtoken->[0] eq 'E' ) {
            my $atag    = q(</) . $dtoken->[1] . q(>);
            my $opentag = q(<) . $dtoken->[1];
            if (   $dirtytext =~ m/\Q$atag\E/isxm
                && $dirtytext !~ m/\Q$opentag\E/isxm )
            {
                $dirtytext =~ s/\Q$atag\E//isxm;
            }
        }
    }
    return $dirtytext;
}

##############################################################################
# Function: removehtmlmarkup
# Parameters:
#
# Description:Remove html markup
##############################################################################

sub removehtmlmarkup {
    my $dirtytext = shift;
    my $idstreame = HTML::TokeParser->new( \$dirtytext )
        or carp "Couldn't parse: $OS_ERROR";
    my $plaintext = q();
    while ( my $setoken = $idstreame->get_token() ) {
        $plaintext .= q( ) . $idstreame->get_trimmed_text();
        ##$plaintext .= $idstreame->get_trimmed_text();
    }
    $plaintext =~ s/(\s)+/ /gis;
    $plaintext =~ s/(\s)+$//gis;
    $plaintext =~ s/^(\s)+//gis;
    return $plaintext;
}

##############################################################################
# Function: removehtmlmarkupbody
# Parameters:
#
# Description: Remove html markup from body
##############################################################################

sub removehtmlmarkupbody {
    my $dirtytext = shift;
    my $idstreamw = HTML::TokeParser->new( \$dirtytext )
        or carp "Couldn't parse: $OS_ERROR";
    my $plaintext = q();
    while ( my $setoken = $idstreamw->get_token() ) {
        $plaintext .= q( ) . $idstreamw->get_trimmed_text();
    }
    if ( length $plaintext < 2 ) {
        $idstreamw = HTML::TokeParser->new( \$dirtytext )
            or carp "Couldn't parse: $OS_ERROR";
        $plaintext = $idstreamw->get_trimmed_text();
    }
    $plaintext =~ s/(\s)+/ /gis;
    $plaintext =~ s/(\s)+$//gis;
    $plaintext =~ s/^(\s)+//gis;
    return $plaintext;
}

##############################################################################
# Function: removehtmlmarkupbodyall
# Parameters:
#
# Description: Remove all html markups from body
##############################################################################

sub removehtmlmarkupbodyall {
    my $dirtytext = shift;
    $dirtytext =~ s/<([^>]+)>//gis;
    return $dirtytext;
}

##############################################################################
# Function: extractpartnumber
# Parameters:
#
# Description: Extract pn or identifier like Doc ID
##############################################################################

sub extractpartnumber {
    my $take_path   = shift;
    my $extractedpn = q();
    ##print "DEBUG:: : PATH: $take_path\n";
    if ( $take_path =~ m/([[:alpha:]](\d){5}([_-](\d){1,2})*)\//gis ) {
        $extractedpn = $1;
        $extractedpn = lc $extractedpn;
        $extractedpn =~ s/_(.*)//gis;
        $extractedpn =~ s/-(.*)//gis;
    }
    elsif ( $take_path =~ m/(([[:upper:]]){5})\//gs ) {
        $extractedpn = $1;
    }
    elsif ( $take_path =~ m/(([0-9]+)-([0-9]+))\//gis ) {
        $extractedpn = $1;
    }
    else {
      my @pathparts = split (/\//, $take_path);
      foreach my $ppaths (@pathparts) {
        if ($ppaths =~ m/^[a-z]{4}$/){
          $extractedpn = $ppaths;
        }
      }
    }

    if (length $extractedpn < 1) {
        $extractedpn = q(generic);
    }
    return $extractedpn;
}

##############################################################################
# Function: writejsonchunk
# Parameters:
#
# Description: Create a file with JSON values
##############################################################################

sub writejsonchunk {
    my $id_json      = shift;
    my $title_json   = shift;
    my $summary_json = shift;
    my $url_json     = shift;
    my $class_passed = shift;
    my $cpth         = shift;
    my $ctitle       = $chaptertitle;
    ##print "DEBUG:: : Called writejsonchunk {id_json: $id_json, title_json: $title_json}\n";
    reinitialize_chunker();
    $thisfilechunkcount++;
    $id_json =~ s/JUSTANID//i;
    if ( length $context < 1 ) { $context = q(all); }
    $url_json =~ s/((.*)[.]ht(m|ml))-(.*)/$1/gis;
    if ( $url_json =~ /^[.][\/]/sxm ) {
        $url_json =~ s/[.]\///sxm;
    }
    $url_json =~ s/^\///sxm;
    #$title_json =~ s/^([.0-9]+)(\s)+//is;
    $indexcounter++;

    my $regx = quotemeta($title_json);
    ##print "DEBUG:: : Replace the '$regx' in '$summary_json' \n";
    if ($summary_json =~ m/^$regx/) {
        $summary_json =~ s/^$regx(\s)+//s;
    }

    my $folderpn = q();
    my $testpn   = extractpartnumber($url_json);
    if ($testpn eq q(generic)) {
        my $pnpath = $url_json;
        $pnpath =~ s/(.*)\/(.*)/$1/gis;
        if (exists $folderpnmapping{$pnpath}) {
          $folderpn = $folderpnmapping{$pnpath};
          ##print "DEBUG:: : Got $folderpn\n";
        }
    }
    elastic_search_mapping($testpn);
    my $book_url = $url_json;
    if ( $book_url =~ m/(.*)\/(.*)/sxm ) {
        $book_url =~ s/(.*)\/(.*)/$1\//gis;
        if ( -f $book_url . q(toc.htm) ) {
            $book_url = $book_url . q(toc.htm);
        }
        elsif ( -f $book_url . q(package-summary.html) ) {
            $book_url = $book_url . q(package-summary.html);
        }
        elsif ( -f $book_url . q(index.htm) ) {
            $book_url = $book_url . q(package-summary.html);
        }
        elsif ( exists $folderpnmapping{$book_url} && -f $book_url . q(index.html) ) {
            $book_url = $book_url . q(index.html);
        }
        else {
            $book_url = $url_json;
        }
    }

    my $json_title_book   = q();
    my $json_release_book = q();
    my $complete_pn       = q();
    ##print "DEBUG:: : testpn: $testpn\n";
    if ( exists $library_data_docid{$testpn} ) {
        ##print "DEBUG:: : Found in 1\n";
        $json_title_book = $library_data_docid{$testpn}[0];
        ##$testpn = $library_data_docid{$testpn}[$SHORTCUT_CHAR_LENGTH_SEVEN];
        $json_release_book
            = $library_data_docid{$testpn}[$SHORTCUT_CHAR_LENGTH_FIVE];
        $complete_pn = $library_data_docid{$testpn}[$SHORTCUT_CHAR_LENGTH_SEVEN];
    }
    elsif ( exists $library_data{$testpn} ) {
        ##print "DEBUG:: : Found in 2\n";
        $json_title_book = $library_data{$testpn}[0];
        ##$testpn = $library_data{$testpn}[$SHORTCUT_CHAR_LENGTH_SEVEN];
        $json_release_book
            = $library_data{$testpn}[$SHORTCUT_CHAR_LENGTH_FIVE];
        $complete_pn = $library_data{$testpn}[$SHORTCUT_CHAR_LENGTH_SEVEN];
    }
    elsif (length $isversionof > 0 && exists $library_data_docid{$isversionof}) {
        $testpn = $isversionof;
        ##print "DEBUG:: : folderpn: $folderpn\n";
        $json_title_book = $library_data_docid{$testpn}[0];
        $json_release_book
            = $library_data_docid{$testpn}[$SHORTCUT_CHAR_LENGTH_FIVE];
        $complete_pn = $library_data_docid{$testpn}[$SHORTCUT_CHAR_LENGTH_SEVEN];
    }
    elsif (length $isversionof > 0 && exists $library_data{$isversionof}) {
        $testpn = $isversionof;
        ##print "DEBUG:: : folderpn: $folderpn\n";
        $json_title_book = $library_data{$testpn}[0];
        $json_release_book
            = $library_data{$testpn}[$SHORTCUT_CHAR_LENGTH_FIVE];
        $complete_pn = $library_data{$testpn}[$SHORTCUT_CHAR_LENGTH_SEVEN];
    }
    elsif (length $folderpn > 0 && exists $library_data{$folderpn}) {
        $testpn = $folderpn;
        ##print "DEBUG:: : folderpn: $folderpn\n";
        $json_title_book = $library_data{$folderpn}[0];
        $json_release_book
            = $library_data{$folderpn}[$SHORTCUT_CHAR_LENGTH_FIVE];
        $complete_pn = $library_data{$folderpn}[$SHORTCUT_CHAR_LENGTH_SEVEN];
    }
    elsif ( exists $additional_data{$testpn} ) {
        ##print "DEBUG:: : Found in 3\n";
        $json_title_book = $additional_data{$testpn}[2];
        $complete_pn          = $additional_data{$testpn}[0];
        $json_release_book
            = $additional_data{$testpn}[$SHORTCUT_CHAR_LENGTH_FOUR];
    }
    else { $json_title_book = q(Not Available.); $complete_pn = q(); $json_release_book = q();}

    if (length $json_title_book < 1 && exists $additional_data{$testpn} && exists $additional_data{$testpn}[2]) {
        $json_title_book = $additional_data{$testpn}[2];
    }
    if (length $complete_pn < 1 && exists $additional_data{$testpn} && exists $additional_data{$testpn}[0]) {
        $complete_pn          = $additional_data{$testpn}[0];
    }
    if (length $json_release_book < 1 && exists $additional_data{$testpn} && exists $additional_data{$testpn}[$SHORTCUT_CHAR_LENGTH_FOUR]) {
        $json_release_book          = $additional_data{$testpn}[$SHORTCUT_CHAR_LENGTH_FOUR] ;
    }
    my $index_container = $url_json;
    $index_container =~ s/(.*)\/(.*)/$2/gsxm;
    #####
    ##  Remove the regex prohibitted chars
    #####
    $index_container =~ s/\{//gis;
    $index_container =~ s/\}//gis;
    $index_container =~ s/\(//gis;
    $index_container =~ s/\)//gis;
    $index_container =~ s/\]//gis;
    $index_container =~ s/\[//gis;
    $index_container =~ s/\*//gis;
    $index_container =~ s/\+//gis;

    #$url_json = $libraryurl.$url_json;

    if ( length $book_url > 0 ) {
        #$book_url = $libraryurl . $book_url;
        #$book_url = $libraryurl . $book_url;
    }
    my $ul_json
        = q(http://www.oracle.com/pls/topic/lookup?ctx=)
        . $context . q(&id=)
        . $id_json;
    if (length $id_json < 1) {
        $ul_json
          = q(http://www.oracle.com/pls/topic/lookup?ctx=)
          . $context;
    }

    my $type_to_take = $testpn;
    if ( $type_to_take =~ m/([[:alpha:]](\d){5}([_-](\d){1,2})*)\//sxm ) {
        $type_to_take = lc $type_to_take;
    }
    $type_to_take =~ s/_(.*)//sxm;
    $type_to_take =~ s/-(.*)//sxm;

    if ( length $title_json > 0 && length $summary_json > 0 ) {
        my $json = q();
        if (length $id_json > 0) {
          $json
            = q(curl -sS -XPUT 'http://)
            . $server_elastic_search
            . q(:9200/)
            . $context . q(/)
            . $type_to_take . q(/)
            . $indexcounter . q(-)
            . $index_container . q(#)
            . $id_json
            . "/_create' -d '{\n";
        }
        else {
          $json
            = q(curl -sS -XPUT  'http://)
            . $server_elastic_search
            . q(:9200/)
            . $context . q(/)
            . $type_to_take . q(/)
            . $indexcounter . q(-)
            . $index_container
            . "/_create' -d '{\n";
        }
        $json_release_lib =~ s/<i>//gis;
        $json_release_lib =~ s/<\/i>//gis;

        $title_json          = jsonify ($title_json);
        $title_json          = jsontitle ($title_json);
        $summary_json        = jsonify ($summary_json);
        $json_title_book     = jsonify ($json_title_book);
        $json_release_lib    = jsonify ($json_release_lib);
        $file_lang           = jsonify ($file_lang);
        $ctitle              = jsonify ($ctitle);
        $file_release_date   = jsonify ($file_release_date);
        $file_description    = jsonify ($file_description);
        $pointer_description = jsonify ($pointer_description);
        $file_keywords       = jsonify ($file_keywords);
        my $computed_topic_type = q();
        if ($javadoc eq q(1)) {
            $computed_topic_type = "API";
        }
        else {
           $computed_topic_type = &get_topic_type(encode_entities_html($title_json), $json_title_book, $url_json, $class_passed); 
        }

        my $url_json_value = $url_json;
        if (length $id_json > 0) {
            $url_json_value = $url_json_value . q(#) . $id_json;
        }

        my $sublibpn      = "";
        my $releasenumber = "";
        my $categoryname      = "";

        my $folderV = $url_json_value;
        $folderV =~ s/(.*)://gis;
        $folderV =~ s/"//gis;
        $folderV =~ s/^(\s)+//gis;
        $folderV =~ s/(\s)+$//gis;
        $folderV =~ s/\\/\//gis;
        # first check with the complete path
        if (length $folderV > 0) {
           my @paths = split(/[\/]/, $folderV);
           for (my $p = 0; $p < (scalar @paths); $p++) {
             my $constructpath = q();
             for (my $pin = 0; $pin < $p; $pin++) {
               $constructpath .= q(/).$paths[$pin];
             }
             $constructpath =~ s/^\///gis;
             $constructpath =~ s/^$library_partnumber//gis;
             my $withunder = format_pn_docarch ($library_partnumber);
             $constructpath =~ s/^$withunder//gis;
             $constructpath =~ s/^\///gis;
             if (exists $subfolder_mappings{$constructpath}) {
               $sublibpn      = $subfolder_mappings{$constructpath}{'PART_NUMBER'};
               $releasenumber = $subfolder_mappings{$constructpath}{'RELEASE_NUMBER'};
               $categoryname      = $subfolder_mappings{$constructpath}{'CATEGORY_NAME'};
               #last; 
            }
           }
        }

        if ((length $sublibpn) < 1) {
            if (exists $subfolder_mappings{$whichpn}){
              $sublibpn      = $subfolder_mappings{$whichpn}{'PART_NUMBER'};
              $releasenumber = $subfolder_mappings{$whichpn}{'RELEASE_NUMBER'};
              $categoryname      = $subfolder_mappings{$whichpn}{'CATEGORY_NAME'};
            }
            else {
              $sublibpn      = $whichpn;
              $releasenumber = "";
              $categoryname      = "";
            }
        }

        $categoryname =~ s/(\s)+//gis;
        $categoryname = lc ($categoryname);
        
        if ($summary_json =~ m/^\Q$title_json\E/) {
            $summary_json =~ s/^\Q$title_json\E//i;
            $summary_json =~ s/^\s+//gis;
            $summary_json =~ s/\s+$//gis;
        }
        if (length $summary_json < 1) {
            return;
        }

        $json .= q("id": ") . $id_json . "\",\n";
        ##$json .= q("title": ") . encode_entities_html($title_json) . "\",\n";
        $json .= q("title": ") . $title_json . "\",\n";
        ##$json .= q("summary": "). encode_entities_html($summary_json) . "\",\n";
        $json .= q("summary": "). $summary_json . "\",\n";
        $json .= q("book_title": ") . $json_title_book . "\",\n";
        $json .= q("part_number": ") . $complete_pn . "\",\n";
        $json .= q("book_release": ") . $json_release_book . "\",\n";
        $json .= q("ul": ") . $ul_json . "\",\n";
        $json .= q("book_url": ") . $book_url . "\",\n";
        $json .= "\"topic_type\": \"".$computed_topic_type."\",\n";
        $json .= "\"roles\": \"".roles($cpth, $json_title_book, part_number, $url_json_value)."\",\n";
        $json .= q("lang": ") . $file_lang . "\",\n";
        ##$json .= q("page_title": ") . encode_entities_html($ctitle) . "\",\n";
        $json .= q("page_title": ") . $ctitle . "\",\n";
        $json .= q("release_date": ") . $file_release_date . "\",\n";
        $json .= q("formats": ") . $book_formats . "\",\n";
        $json .= q("libraryurl": ") . $libraryurl . "\",\n";
        $json .= q("url": ") . $url_json_value . "\",\n";

        if (length $pointer_description > 0) {
            if (length $file_description > 0) {
              $json .= q("description": ") . $file_description.q(;).$pointer_description. "\",\n";
            }
            else {
              $json .= q("description": ") . $pointer_description . "\",\n";
            }
            $pointer_description = q();
        }
        else {
          $json .= q("description": ") . $file_description . "\",\n";
        }
        $json .= q("mainpn": ") . $whichpn . "\",\n";
        $json .= q("librarypn": ") . $sublibpn . "\",\n";
        $json .= q("category_name": ") . $categoryname . "\",\n";
        $json .= q("release_number": ") . standardize_release_number($releasenumber) . "\",\n";
        $json .= q("keywords": ") . $file_keywords . "\"\n";
        $json .= "}'\n";

        open my $CHUNK, '>>',
            $jsonoutputfolder . q(/) . $library_partnumber . q(.txt)
            or croak "Cannot open for reading: $OS_ERROR ".$jsonoutputfolder . q(/) . $library_partnumber . q(.txt);
        binmode $CHUNK, ':encoding(UTF-8)';
        #binmode $CHUNK;
        print {$CHUNK} $json . "\n\n";
        print {$CHUNK} q(VIVEK-SAMPLE) . "\n\n";
        close $CHUNK
            or carp "Can't close : $OS_ERROR";
        $summary_count++;
    }
    return;
}
##############################################################################
#
# Function: jsonify
#
# escapes to the valid json text
##############################################################################

sub jsonify {
    my $jsondata = shift;
    $jsondata =~ s/^(\r)+//gis;
    $jsondata =~ s/^(\n)+//gis;
    $jsondata =~ s/(\r)+$//gis;
    $jsondata =~ s/(\n)+$//gis;
    $jsondata =~ s/(\r)*//gis;
    $jsondata =~ s/(\n)+/ /gis;
    $jsondata =~ s/&nbsp;/ /gis;
    $jsondata =~ s/\\/\\\\/gis;
    $jsondata =~ s/"/\\"/gis;
    $jsondata =~ s/“/\\"/gis;
    $jsondata =~ s/‘/'/gis;
    $jsondata =~ s/’/'/gis;
    $jsondata =~ s/”/\\"/gis;
    $jsondata =~ s/–/-/gis;
    $jsondata =~ s/(\s)+[,](\s)+/, /gis;
    $jsondata =~ s/(\s)+[.](\s)+/. /gis;
    $jsondata =~ s/(\s)+[;](\s)+/. /gis;
    $jsondata =~ s/(\t)+/ /gis;
    return $jsondata;
}

##############################################################################
# Function: verify_chunk
# Parameters:
#
# Description: Verify chunk and remove the duplicate starting part.
##############################################################################

sub verify_chunk {
    my $hd = shift;
    my $bd = shift;
    $hd = removehtmlmarkupbodyall($hd);
    $bd = removehtmlmarkupbodyall($bd);
    ##print "DEBUG:: VERIFY CHUNK: '$hd','$bd'\n";
    if ( $hd =~ m/^\Q$bd\E$/ || length ($bd) <= length ($hd)) {
        ##print "DEBUG:: VERIFY CHUNK: 0\n";
        return 0;
    }
    $bd =~ s/^\Q$hd\E//gis;
    $bd =~ s/^(\s)+//gis;
    $bd =~ s/(\s)+$//gis;
    $bd =~ s/(\s)+//gis;
    $hd =~ s/(\s)+//gis;

    if ( $hd =~ m/^\Q$bd\E$/sxm || length ($bd) <= length ($hd)) {
        ##print "DEBUG:: VERIFY CHUNK: 1\n";
        return 0;
    }
    ##print "DEBUG:: VERIFY CHUNK: 1\n";
    return 1;
}

##############################################################################
# Function: get_descriptor
# Parameters:
#     Part Number
# Description:
#     Takes the Library Part Number and generates and fetches the XML
##############################################################################

sub get_descriptor {
    my $librarypn = shift;
    $librarypn = format_pn($librarypn);
    my $xml_data       = q();
    my $pdb_url_to_use = q();

    my $ua = LWP::UserAgent->new();

    if ( $pdb_url_to_use =~ m{ stdoc }xms ) {
        $ua->credentials( 'stdoc.us.oracle.com', q(), q(), q() );
    }
    else {
        $ua->credentials( 'pdb.us.oracle.com', q(), q(), q() );
    }

    $ua->proxy( [ 'http', 'ftp' ], 'http://www-proxy.us.oracle.com:80' );
    $ua->no_proxy(
        'oracle.com',       'oracleleads.com',
        'us.oracle.com',    'uk.oracle.com',
        'ca.oracle.com',    'oraclecorp.com',
        'oracleportal.com', 'ie.oracle.com'
    );

    print 'Posting: ' . $pdb_url . 'ip.jsp?pn=' . $librarypn . "\n";

    my $response = $ua->post( $pdb_url . 'ip.jsp?pn=' . $librarypn.'&c=y' );

    if ( $response->is_success() ) {

        # So the XML is now generated on the server. Get it
        print 'Reading XML: '
            . $pdb_url . 'xml/'
            . format_pn_docarch($librarypn) . '.xml';

        $response = $ua->get(
            $pdb_url . 'xml/' . format_pn_docarch($librarypn) . '.xml' );

        if ( $response->is_success() ) {
            $xml_data = $response->content();
        }
        else {
            $errors{'Error while reading the descriptor'}
                = $response->status_line;
        }

    }
    else {
        $errors{'Error while fetching the descriptor'}
            = $response->status_line;
    }

    return $xml_data;
}

##############################################################################
# Function: format_pn
# Parameters:
#     Part Number
# Description:
#     Takes the part number and uppercases and converts the underscore to hyphen
##############################################################################

sub format_pn {
    my $raw_pn = shift;

    $raw_pn = uc $raw_pn;
    $raw_pn =~ s{_}{-}xms;

    return $raw_pn;
}

##############################################################################
# Function: format_pn_docarch
# Parameters:
#     Part Number
# Description:
#     Takes the part number and uppercases and converts the hyphen to underscore
##############################################################################

sub format_pn_docarch {
    my $raw_pn = shift;

    $raw_pn = uc $raw_pn;
    $raw_pn =~ s{ - }{_}xms;

    return $raw_pn;
}

##############################################################################
# Function: format_pn_lower
# Parameters:
#     Part Number
# Description:
#     Takes the part number and lowercases and removes hyphen/underscore
##############################################################################

sub format_pn_lower {
    my $raw_pn = shift;

    $raw_pn = lc $raw_pn;
    $raw_pn =~ s{ [-_](.*) }{}xms;
    if ( $raw_pn =~ m/mglos/isxm ) {
        $raw_pn = 'm-glos';
    }
    if ( $raw_pn =~ m/mindx/isxm ) {
        $raw_pn = 'm-indx';
    }
    return $raw_pn;
}

##############################################################################
# Function: print_errors
# Parameters:
#
# Description: Print the errors
##############################################################################

sub print_errors {

    for my $keys ( keys %errors ) {
        print 'Error: ' . $keys . "\n";
        print 'Description: ' . $errors{$keys} . "\n";
    }

    exit;
}

##############################################################################
# Function: build_data
# Parameters:
#     part number
# Description:
#     Takes a part number and builds up the library data hash
##############################################################################

sub build_data {
    my $library_pn  = shift;
    my $scan_folder = shift;
    my $xml_data    = get_descriptor($library_pn);

    if ( ( scalar keys %errors ) > 0 ) {
        #print_errors();
    }
    else {
        parse_xml( $xml_data, $scan_folder );
        if ( ( scalar keys %errors ) > 0 ) {
            print_errors();
        }
    }

    # At this point, there would be the xml file in the string. Parse it!

    # At this point, the data hash is built!
    return;
}

##############################################################################
# Function: parse_xml
# Parameters:
#     XML Data
# Description:
#     Takes the XML String and validates, parses, and builds the data hash
##############################################################################

sub parse_xml {
    my $xml_data    = shift;
    my $scan_folder = shift;
    my $parser      = XML::LibXML->new();
    my $doc;
    my $counter  = 0;
    my $alltotal = 0;
    $doc = $parser->parse_string($xml_data);

    my $library = $doc->getDocumentElement();
    $library->findnodes('library');
    my $prodattr   = 'product';
    my $relnumattr = 'releasenumber';
    my $relvalattr = 'releasevalue';
    my $partnoattr = 'partno';
    my $titleattr  = 'title';
    my $prodtitle  = $library->findvalue( q(@) . $prodattr );
    for ( $library->findnodes('category') ) {

        for ( $_->findnodes('document') ) {
            my $partno_add = $_->findvalue('@partno');
            my $complete_pn = $partno_add;
            $partno_add = lc $partno_add;
            $partno_add =~ s/-(.*)//sxm;
            $partno_add =~ s/_(.*)//sxm;
            my $docid_add = $_->findvalue('@docid');
            $docid_add = uc $docid_add;
            my $title_add = $_->findvalue('@title');
            my $title_prod = $_->findvalue('@product');
            $title_add =~ s/^$title_prod//i;
            $title_add =~ s/^( )+//;
            $title_add =~ s/( )+$//;
            $title_add = encode_entities_html($title_add);
            my $product_name_title_add = $_->findvalue('@product');
            my $book_release           = $_->findvalue('@releasevalue');
            $product_name_title_add =~ s/\+/\\+/gis;
            $product_name_title_add =~ s/\*/\\*/gis;
            $product_name_title_add
                = encode_entities_html($product_name_title_add);
            $additional_data{$partno_add} = [
                $complete_pn, $docid_add,
                $title_add,  $product_name_title_add,
                $book_release
            ];
            $additional_data{$docid_add} = [
                $complete_pn, $docid_add,
                $title_add,  $product_name_title_add,
                $book_release
            ];

        }
    }

    $prodtitle = encode_entities_html($prodtitle);
    my $rn = $library->findvalue( q(@) . $relnumattr );
    $rn =~ s{ [.] }{}xmsg;
    my $librel          = $library->findvalue( q(@) . $relvalattr );
    my $initial_release = q();
    my $final_release   = q();
    if ($librel) {
        if ( $librel =~ m/(([\d]+)([[:lower:]]+))(\s)+/isxm ) {
            my $rel_first = $1;
            $initial_release = $rel_first;
            my $digit_rel   = $2;
            my $charitalics = $3;
            $final_release = $digit_rel . q(<i>) . $charitalics . q(</i>);
            $librel =~ s/$1/$digit_rel<i>$charitalics<\/i>/gis;
        }
    }
    $library_data{ $library->findvalue( q(@) . $partnoattr ) } = [
        $prodtitle . q( ) . $library->findvalue( q(@) . $titleattr ),  # Title
        $prodtitle,    # Product Name
        q(),           # Platform
        q(),           # feature
        q(),           # category
        ##$library->findvalue( q(@) . $relvalattr ),    # Release Value
        $librel,       # Release Value
    ];

    ## build data from PDB as well so as to fill the missing values

    # now scan the html files and build the info.
    find( { wanted => \&wanted_all_files, no_chdir => 1 }, $scan_folder );

    my $partno_scanned   = q();
    my $doctitle_scanned = q();
    my $prod_scanned     = q();
    my $platform_scanned = q();
    my $feature_scanned  = q();
    my $category_scanned = q();
    my $release_scanned  = q();
    my $docid            = q();
    my $firsth1          = q();
    my $lpartno          = q();
    my $pagetitle        = q();

    for my $htm_file_of_lib (@html_files_from_library) {
        ##print "DEBUG:: : Parsing: $htm_file_of_lib\n";
        open my $SCANNER, '<', $htm_file_of_lib
            or carp "Can't read $htm_file_of_lib: $OS_ERROR";
        my @file_scanned = <$SCANNER>;
        close $SCANNER
            or carp "Can't close $htm_file_of_lib: $OS_ERROR";

        my $scanned_file_joined = join q(), @file_scanned;
        undef @file_scanned;
        
        if (   $scanned_file_joined =~ m{ <[?]xml [^>]+ encoding [[:space:]]* = [[:space:]]* ['"] utf -? 8 }xmsi
            || $scanned_file_joined =~ m{ <meta [^>]+ charset [[:space:]]* = [[:space:]]* utf -? 8 }xmsi )
        {
            $scanned_file_joined = Encode::decode( 'utf8', $scanned_file_joined );
        }


        my $idstream = HTML::TokeParser->new( \$scanned_file_joined )
            or print "Couldn't parse: $OS_ERROR";
        my $tocleftvalign = 0;
        my $maintitlefrompage = q();
        while ( my $token = $idstream->get_token() ) {

            if (   length $partno_scanned > 0
                && length $doctitle_scanned > 0
                && length $prod_scanned > 0
                && length $docid > 0
                && length $release_scanned > 0 )
            {
                last;
            }
            if ( !$token->[0] || !$token->[1] || !$token->[2] ) {
                next;
            }
            if ($token->[0] eq 'S'    # doctitle
                && $token->[1] eq 'title'
                )
            {
                $pagetitle = $idstream->get_trimmed_text('/title');
                if ( $pagetitle =~ m/(.*)(master(\s)*glossary)(.*)/isxm ) {
                    $doctitle_scanned = $2;
                    $release_scanned  = $4;
                    $prod_scanned     = $1;
                    $docid            = 'DOCID';
                    $partno_scanned   = 'MGLOS';
                    last;
                }
                elsif ( $pagetitle =~ m/(.*)(master(\s)*index)(.*)/isxm ) {
                    $doctitle_scanned = $2;
                    $release_scanned  = $4;
                    $prod_scanned     = $1;
                    $docid            = 'DOCID';
                    $partno_scanned   = 'MINDX';
                    last;
                }
                elsif ( lc $pagetitle ne 'contents' ) {
                    ##print "DEBUG:: : 1: $doctitle_scanned\n";
                    ##$doctitle_scanned = $pagetitle;
                }
            }
            if ($token->[0] eq 'S'    # doctitle
                && $token->[1] eq 'meta'
                && exists $token->[2]{'name'}
                && ($token->[2]{'name'} eq 'docid' || $token->[2]{'name'} =~ m/isVersionOf/)
                )
            {
                $docid = $token->[2]{'content'};
            }
            if ($token->[0] eq 'S'    # doctitle
                && $token->[1] eq 'meta'
                && exists $token->[2]{'name'}
                && ($token->[2]{'name'} =~ m/title/)
                )
            {
                $maintitlefrompage = $token->[2]{'content'};
                ## add logic to extract the release number from here
            }
            if ($token->[0] eq 'S'    # doctitle
                && $token->[1] eq 'meta'
                && exists $token->[2]{'name'}
                && ($token->[2]{'name'} eq 'doctitle' || $token->[2]{'name'} =~ m/dcterms.title/)
                )
            {
                $doctitle_scanned = $token->[2]{'content'};
                ## add logic to extract the release number from here
            }
            if ($token->[0] eq 'S'    # partno
                && $token->[1] eq 'meta'
                && exists $token->[2]{'name'}
                && ($token->[2]{'name'} =~ m/dcterms.identifier/)
                )
            {
                $partno_scanned = $token->[2]{'content'};
            }
            if ($token->[0] eq 'S'    # partno
                && $token->[1] eq 'meta'
                && exists $token->[2]{'name'}
                && ($token->[2]{'name'} eq 'partno' || $token->[2]{'name'} =~ m/partno/)
                )
            {
                $lpartno = $token->[2]{'content'};
            }

            if ($token->[0] eq 'S'    # docinfo
                && $token->[1] eq 'h1'
                && exists $token->[2]{'class'}
                && $token->[2]{'class'} eq 'docinfo'
                )
            {
                $prod_scanned = $idstream->get_trimmed_text('/h1');
                $firsth1 = $prod_scanned ;
                ##print "DEBUG:: : INSIDE1 H1\n";
            }
            elsif ($token->[0] eq 'S'    # docinfo
                && $token->[1] eq 'h1'
                )
            {
                $firsth1 = $idstream->get_trimmed_text('/h1');
                ##print "DEBUG:: : INSIDE2 H1\n";
            }
            if ($token->[0] eq 'S'    # prodname
                && ( $token->[1] eq 'span' || $token->[1] eq 'p' )
                && exists $token->[2]{'class'}
                && lc $token->[2]{'class'} eq 'booktitle' ##&& length ($doctitle_scanned) < 1
                )
            {
                $doctitle_scanned
                    = $idstream->get_trimmed_text( q(/) . $token->[1] );
                if ( length $firsth1 > 0 ) {
                    $doctitle_scanned = $firsth1 . q( ) . $doctitle_scanned;
                    $prod_scanned     = $firsth1;
                }
                if ( length $prod_scanned > 0 ) {
                    $doctitle_scanned = $prod_scanned . q( ) . $doctitle_scanned;
                }
                ##print "DEBUG:: : dcterms title: $doctitle_scanned\n";
            }

            if ($token->[0] eq 'S'    # prodname
                && $token->[1] eq 'td'
                && exists $token->[2]{'align'}
                && lc $token->[2]{'align'} eq 'left'
                && exists $token->[2]{'valign'}
                && lc $token->[2]{'valign'} eq 'top'
                && $tocleftvalign < 1
                )
            {
                $tocleftvalign++;
                $doctitle_scanned = $idstream->get_trimmed_text('br');
                $idstream->get_token();
                $release_scanned = $idstream->get_trimmed_text('/b');
                if ( $release_scanned =~ m/(.*?)(for(.*))/isxm ) {
                    $release_scanned = $1;
                    my $platformhere = $2;
                    $release_scanned =~ s{ / \z}{}xms;
                    $doctitle_scanned
                        = $doctitle_scanned . q( ) . $platformhere;
                    $doctitle_scanned =~ s{ / \z}{}xms;
                }
                $idstream->get_token();
                $partno_scanned = $idstream->get_trimmed_text('/td');
                if ( length $docid < 1 ) {
                    $docid = 'DOCID';
                }
                if ( length $partno_scanned < 1 ) {
                    $partno_scanned = 'PARTNO-' . $docid;
                }
                $prod_scanned = q(Oracle&reg;);
            }

            if ($token->[0] eq 'S'    # prodname
                && ( $token->[1] eq 'span' || $token->[1] eq 'p' )
                && exists $token->[2]{'class'}
                && lc $token->[2]{'class'} eq 'invpartnumber'
                )
            {
                $partno_scanned
                    = $idstream->get_trimmed_text( q(/) . $token->[1] );
            }
            if ($token->[0] eq 'S'    # prodname
                && ( $token->[1] eq 'span' || $token->[1] eq 'p' )
                && exists $token->[2]{'class'}
                && lc $token->[2]{'class'} eq 'revnumber'
                )
            {
                $release_scanned = $idstream->get_trimmed_text('/p');
                $release_scanned =~ s/for(.*)//gis;
                $release_scanned =~ s/^(\s)*//gis;
            }

            if ($token->[0] eq 'S'    # prodname
                && ( $token->[1] eq 'td' )
                && exists $token->[2]{'class'}
                && $token->[2]{'class'} eq 'zz-nav-header-cell'
                )
            {
                my $completetext = $idstream->get_trimmed_text('/td');
                if ( $completetext
                    =~ m/(.*?)(release[ ]+[\d]+(.*?))((.*?)($PARTNO))/gis )
                {
                    $release_scanned  = $3;
                    $partno_scanned   = $6;
                    $doctitle_scanned = $1;
                    $release_scanned =~ s/[\s]+$//gis;
                    $release_scanned =~ s/^[\s]+//gis;
                    $release_scanned =~ s/[\s]+/ /gis;
                    $partno_scanned =~ s/[\s]+$//gis;
                    $partno_scanned =~ s/^[\s]+//gis;
                    $partno_scanned =~ s/[\s]+/ /gis;
                    $doctitle_scanned =~ s/[\s]+$//gis;
                    $doctitle_scanned =~ s/^[\s]+//gis;
                    $doctitle_scanned =~ s/[\s]+/ /gis;
                    $doctitle_scanned =~ s/^Oracle([^(\s)])*(\s)*//xmsgi;
                    $doctitle_scanned =~ s{\A Oracle }{}xmsgi;
                    $prod_scanned = $doctitle_scanned;
                    $docid        = q(DOCID);
                }
            }

            if ( $htm_file_of_lib =~ m/constant-values/isxm )    #javadoc
            {
                my $titleval = q();
                if (   $token->[0] eq 'S'
                    && $token->[1] eq 'td'
                    && exists $token->[2]{'align'}
                    && $token->[2]{'align'} eq 'right'
                    && exists $token->[2]{'valign'}
                    && $token->[2]{'valign'} eq 'top'
                    && exists $token->[2]{'rowspan'}
                    && $token->[2]{'rowspan'} eq '3' )
                {
       # prodname would have got extracted. remove the "Constant Field Values"
                    ##$titleval = $idstream->get_trimmed_text('/td');
                    $doctitle_scanned = $idstream->get_trimmed_text('br');
                    $idstream->get_token();
                    $release_scanned = $idstream->get_trimmed_text('br');
                    $idstream->get_token();
                    $partno_scanned = $idstream->get_trimmed_text('/td');
                    $docid          = 'DOCID';
                }
                elsif ($token->[0] eq 'S'
                    && $token->[1] eq 'div'
                    && exists $token->[2]{'class'}
                    && $token->[2]{'class'} eq 'aboutLanguage' )
                {
                    $doctitle_scanned = $idstream->get_trimmed_text('br');
                    $idstream->get_token();
                    $release_scanned = $idstream->get_trimmed_text('br');
                    $idstream->get_token();
                    $partno_scanned = $idstream->get_trimmed_text('/div');
                    $docid          = 'DOCID';
                }
                ##elsif ($token->[0] eq 'S'
                ##    && $token->[1] eq 'div'
                ##    && exists $token->[2]{'class'}
                ##    && $token->[2]{'class'} eq 'aboutLanguage' )
                ##{
                ##    $titleval = $idstream->get_trimmed_text('/div');
                ##}

                if (length $titleval > 0
                    && (   length $partno_scanned < 1
                        || length $release_scanned < 1
                        || length $doctitle_scanned < 1 )
                    )
                {
                    $prod_scanned =~ s/\QConstant Field Values\E//gis;
                    $prod_scanned =~ s/^(\W)+/ /gis;
                    $prod_scanned =~ s/(\W)+$/ /gis;
                    $prod_scanned =~ s/^\s+//gis;
                    $prod_scanned =~ s/\s+$//gis;
                    $prod_scanned
                        =~ s/(([[:alpha:]])(.*)([[:alpha:]]))/$1/gis;
                    $prod_scanned =~ s/^Oracle([^(\s)])*(\s)*//xmsgi;
                    $prod_scanned =~ s{\A Oracle }{}xmsgi;

                    # Remove Oracle (and/or reg symbol)
                    my $titlevaltemp = $titleval;
                    $titlevaltemp =~ s/^Oracle([^(\s)])*(\s)*//xmsgi;
                    $titlevaltemp =~ s{\A Oracle }{}xmsgi;
                    $titlevaltemp =~ s/\Q$prod_scanned\E//xmsgi;
                    $titlevaltemp =~ s/^(\s)*//gis;
                    $titlevaltemp =~ s/(\s)*$//gis;
                    if ( $titlevaltemp =~ m/($PARTNO)/xms ) {
                        $partno_scanned = $1;
                        $titlevaltemp =~ s/\Q$partno_scanned\E//gis;
                        $titlevaltemp =~ s/^(\s)*//gis;
                        $titlevaltemp =~ s/(\s)*$//gis;
                        $release_scanned = $titlevaltemp;
                        $titleval =~ s/\Q$partno_scanned\E//gis;
                        $titleval =~ s/\Q$release_scanned\E//gis;
                        $titleval =~ s/^(\s)*//gis;
                        $titleval =~ s/(\s)*$//gis;
                        $doctitle_scanned = $titleval;
                        $docid            = 'DOCID';
                    }
                }
            }
        }
        ##if (length $doctitle_scanned < 1 && length $maintitlefrompage > 0) {
        ##    $doctitle_scanned = $maintitlefrompage;
        ##}
        ##print "DEBUG:: : FIRSTH1: $firsth1\n";
        my $prname = $firsth1;
        $prname =~ s{\A Oracle® }{}xmsgi;
        $prname =~ s{\A Oracle[&\#\d;[:alpha:]]+ }{}xmsgi;
        $prname =~ s{\A Oracle }{}xmsgi;
        $prname =~ s/^( )+//is;
        $prname =~ s/( )+$//is;
        ##print "DEBUG:: : prname: $prname\n";
        my $titlefound = 0;
        if (length $pagetitle > 0) {
           ##print "DEBUG:: : At start 1: $doctitle_scanned\n";
           ##print "DEBUG:: : At start 1c: $pagetitle\n";
           my $pgtitlewitouttrademark = $pagetitle;
           $pgtitlewitouttrademark =~ s{\A Oracle® }{}xmsgi;
           $pgtitlewitouttrademark =~ s{\A Oracle[&\#\d;[:alpha:]]+ }{}xmsgi;
           $pgtitlewitouttrademark =~ s{\A Oracle }{}xmsgi;
           $pgtitlewitouttrademark =~ s/^( )+//is;
           $pgtitlewitouttrademark =~ s/( )+$//is;
           ##print "DEBUG:: : At start 1c1:$pgtitlewitouttrademark:$prname:\n";
           if (length $prname > 0 && length $pgtitlewitouttrademark > 0 && $pgtitlewitouttrademark ne $prname) {
               $doctitle_scanned = $pgtitlewitouttrademark;
               ##print "DEBUG:: : At start 1c2:$doctitle_scanned:\n";
               $titlefound = 1;
           }
        }

        if (! $titlefound && length $maintitlefrompage > 0) {
           ##print "DEBUG:: : At start 2: $doctitle_scanned\n";
           ##print "DEBUG:: : At start 2c: $maintitlefrompage\n";
           my $mntitlewitouttrademark = $maintitlefrompage;
           $mntitlewitouttrademark =~ s{\A Oracle® }{}xmsgi;
           $mntitlewitouttrademark =~ s{\A Oracle[&\#\d;[:alpha:]]+ }{}xmsgi;
           $mntitlewitouttrademark =~ s{\A Oracle }{}xmsgi;
           $mntitlewitouttrademark =~ s/^( )+//is;
           $mntitlewitouttrademark =~ s/( )+$//is;

           ##print "DEBUG:: : prname: $prname\n";
           ##print "DEBUG:: : mntitlewitouttrademark: $mntitlewitouttrademark\n";
           ##print "DEBUG:: : At start 1c1:$mntitlewitouttrademark:$prname:\n";
           if (length $prname > 0 && length $mntitlewitouttrademark > 0 && $mntitlewitouttrademark ne $prname) {
               $doctitle_scanned = $mntitlewitouttrademark;
               ##print "DEBUG:: : At start 2c2:$doctitle_scanned:\n";
           }
        }
        # enter the values to library_data
        if (   length $partno_scanned < 1
            || length $doctitle_scanned < 1 )
        {
            ##print "RETRYING: $partno_scanned : $doctitle_scanned : $prod_scanned : $docid : $release_scanned\n";
            $idstream = HTML::TokeParser->new( \$scanned_file_joined )
                or print "Couldn't parse: $OS_ERROR";
            while ( my $token = $idstream->get_token() ) {
                my $alltext = $idstream->get_trimmed_text('/body');
                if ( $alltext =~ m/($PARTNO)/gis ) {
                    $partno_scanned = $1;
                    ##print q(Part No.: ) . $partno_scanned . "\n";
                    last;
                }
            }
            if ( length $doctitle_scanned > 0 && length $prod_scanned < 1 ) {
                $prod_scanned = $doctitle_scanned;
                $docid        = q(DOCID);
            }
            if ( length $doctitle_scanned < 1 && length $prod_scanned > 0 ) {
                $doctitle_scanned = $prod_scanned;
                $docid            = q(DOCID);
            }
        }
        if (   length $partno_scanned > 0
            && length $doctitle_scanned > 0 )
        {
            ##print "DEBUG:: : 1: $doctitle_scanned\n";
            if ( $partno_scanned =~ m/($PARTNO)/xms ) {
                $partno_scanned = $1;
            }
            $prod_scanned = encode_entities_html($prod_scanned);
            $doctitle_scanned
                = encode_entities_html($doctitle_scanned);
            if ( $doctitle_scanned
                =~ m/Oracle[&\#\d;[:alpha:]]+(\s)*Database/gis )
            {
                ##$doctitle_scanned
                ##    =~ s{Oracle[&\#\d;[:alpha:]]+(\s)*Database}{}xmsg;
            }
            $doctitle_scanned =~ s{\A Oracle® }{}xmsgi;
            $doctitle_scanned =~ s{\A Oracle[&\#\d;[:alpha:]]+ }{}xmsgi;
            $doctitle_scanned =~ s{\A Oracle }{}xmsgi;
            $doctitle_scanned =~ s{\A Cloud }{}xmsgi;
            $doctitle_scanned =~ s{ \Q$release_scanned\E}{}xmsgi;
            $doctitle_scanned =~ s{ \(\s*\)}{}xmsgi;
            $doctitle_scanned =~ s{\A \s+ }{}xmsgi;
            $doctitle_scanned =~ s{ \s+ \z}{}xmsgi;
            my $complete_pn = $partno_scanned;
            $partno_scanned =~ s{ _ .* }{}xmsgi;
            $partno_scanned =~ s{ - .* }{}xmsgi;
            $partno_scanned = lc $partno_scanned;
            $counter++;

            ##print "DEBUG:: : 2: $doctitle_scanned\n";
            if ( length $initial_release > 0 && length $final_release > 0 ) {
                $doctitle_scanned =~ s/$initial_release/$final_release/gis;
            }
            ##print "DEBUG:: : 3: $doctitle_scanned\n";

            $library_data{$partno_scanned} = [
                appropriate_titles($doctitle_scanned),
                $prod_scanned,     $platform_scanned, $feature_scanned,
                $category_scanned, $release_scanned,  $docid,
                $complete_pn
            ];
            $library_data_docid{$docid} = [
                appropriate_titles($doctitle_scanned),
                $prod_scanned,     $platform_scanned, $feature_scanned,
                $category_scanned, $release_scanned,  $docid,
                $complete_pn
            ];
            my $whichfolder = $htm_file_of_lib;
            $whichfolder =~ s/^[.]\///gis;
            $whichfolder =~ s/^\///gis;
            $whichfolder =~ s/(.*)\/(.*)/$1/gis;
            $folderpnmapping{$whichfolder} = $partno_scanned;
        }
        else {
            ## print "FAILED: $partno_scanned : $doctitle_scanned : $prod_scanned : $docid : $release_scanned\n";
        }
        $partno_scanned   = q();
        $doctitle_scanned = q();
        $prod_scanned     = q();
        $platform_scanned = q();
        $feature_scanned  = q();
        $category_scanned = q();
        $release_scanned  = q();
        $docid            = q();
        $lpartno          = q();
    }
    return;
}

##############################################################################
# Function: appropriate_titles
# Parameters:
#
# Description: Convert the titles to appropriate representation.
##############################################################################

sub appropriate_titles {
    my $raw_title = shift;
    $raw_title =~ s/&\#x00AE;//gis;
    $raw_title =~ s/&reg;//gis;
    if (   $raw_title =~ m/^Client(\s)+Installation/isxm
        || $raw_title =~ m/^Client(\s)+Quick(\s)+Installation/isxm
        || $raw_title =~ m/^Client(\s)+Quick(\s)+Installation/isxm
        || $raw_title =~ m/^Clusterware/isxm
        || $raw_title =~ m/^Examples/isxm
        || $raw_title =~ m/^Gateway/isxm
        || $raw_title =~ m/^Installation(\s)+Guide/isxm
        || $raw_title =~ m/^Quick(\s)+Installation(\s)+Guide/isxm
        || $raw_title =~ m/^Vault(\s)+/isxm )
    {
        $raw_title = 'Database ' . $raw_title;
    }

    if (   $raw_title =~ m/^C[+][+](\s)+Call(\s)+Interface/isxm
        || $raw_title =~ m/^Call(\s)+Interface(\s)+Programmer/isxm )
    {
        $raw_title = 'Oracle ' . $raw_title;
    }

    if ( $raw_title =~ m/Java(\s)+API(\s)+Reference$/isxm ) {
        $raw_title = $raw_title . ' (Javadoc)';
    }
    $raw_title =~ s/,(\s)*/ /isxm;
    $raw_title =~ s/^(\s)*//isxm;
    $raw_title =~ s/(\s)*$//isxm;
    return $raw_title;
}

##############################################################################
#
# Function: wanted_all_files
#
# Parameter: filename
# builds toc and title array
#
##############################################################################

sub wanted_all_files {
    my $temp = $_;

    if (   $temp =~ m{  title[.]html? }xms
        || $temp =~ m{ toc[.]html? }xms )
    {
        if ( $temp =~ m/(.*)toc[.]ht[m|ml]/gis ) {
            my $checkpath = $1;
            my $keeppath  = $checkpath;
            $checkpath = $checkpath . 'title.htm';
            $keeppath  = $keeppath . 'constant-values.html';
            if ( -f $checkpath ) {
                if ( !any { $_ eq $checkpath } @html_files_from_library ) {
                    push @html_files_from_library, $checkpath;
                }
            }
            elsif ( -f $keeppath ) {
                if ( !any { $_ eq $keeppath } @html_files_from_library ) {
                    push @html_files_from_library, $keeppath;
                }
            }
            elsif ( !any { $_ eq $checkpath } @html_files_from_library ) {
                push @html_files_from_library, $temp;
            }
        }
        else {
            push @html_files_from_library, $temp;
        }
    }

    return;
}



##############################################################################
#
# Function: get_topic_type
#
# Parameter: sec_title, book_name, fname_type, topic_class
# determines the topic type for the search result.
#
##############################################################################

sub get_topic_type {
   my $sec_title     = shift;
   my $book_title    = shift;
   my $fname_type    = shift;
   my $topic_class   = shift;
   my $type_of_topic = q();

   my $is_concept_type = is_concepts($sec_title, $book_title, $fname_type);
   my $is_task_type    = is_tasks($sec_title);
   my $is_ref_type     = is_references($book_title, $sec_title);
   my $is_gloss_type   = is_glossary($topic_class);
   my $is_chapter_type = is_chapter($topic_class);
   my $is_example_type = is_example($sec_title);
   my $is_faq_type     = is_faq($sec_title);
   my $is_error_type   = is_error_message($sec_title, $book_title);

   if ($is_concept_type eq q(1)) {$topic_types_found{q(concepts)}++; $type_of_topic .= q(,concepts);}
   if ($is_task_type eq q(1)) {$topic_types_found{q(tasks)}++; $type_of_topic .= q(,tasks);}
   if ($is_ref_type eq q(1)) {$topic_types_found{q(references)}++; $type_of_topic .= q(,references);}
   if ($is_gloss_type eq q(1)) {$topic_types_found{q(glossary)}++; $type_of_topic .= q(,glossary);}
   if ($is_chapter_type eq q(1)) {$topic_types_found{q(chapter)}++; $type_of_topic .= q(,chapter);}
   if ($is_example_type eq q(1)) {$topic_types_found{q(example)}++; $type_of_topic .= q(,example);}
   if ($is_faq_type eq q(1)) {$topic_types_found{q(faq)}++; $type_of_topic .= q(,faq);}
   if ($is_error_type eq q(1)) {$topic_types_found{q(error)}++; $type_of_topic .= q(,error_message);}

   $type_of_topic =~ s/^,//sxm;
   $type_of_topic =~ s/,$//sxm;
   return $type_of_topic;
}

##############################################################################
#
# Function: is_concepts
#
# Parameter: sec_title, book_name, fname_type
# Determines if the topic is of type concepts
##############################################################################

sub is_concepts {
   my $sec_title = shift;
   my $book_title = shift;
   my $fname_type = shift;
   my $is_intro = q(0);
   if ($fname_type =~ m/toc[.]htm/sxm) {return q(0);}
   my @concepts_strings = ('^Why _se(\s)*.*', '^Features.*', '^Advantages.*', '^Benefits.*',
                           '^Introduc.*', '^What _s(\s)*.*', '^What _re(\s)*.*', '^What(\s)*.*?',
                           '^Who(\s)*.*?', '^When(\s)*.*?', '^When _o(\s)*.*', '^Where(\s)*.*?',
                           '^Why(\s)*.*?', '^Learning.*', '^Choosing.*', '^Understanding.*',
                           '.*Deciding.*','^About.*','.*Planning.*','.*Overview.*',
                           '.*Typical.*','.*Concept.*','.*Guidelines.*','.*Highlights.*',
                           '.*Consideration.*','.*Restriction.*','.*Limits.*',
                           '.*Limitations.*','.*Architectur.*','.*Primer',
                           '.*Getting(\s)Started.*','.*at(\s)*a(\s)*Glance','.*Nutshell',
                           '.*FAQ.*','.*Roadmap.*','.*Cookbook.*','.*VERSUS.*','.*(\s)VS(\s)*.*',
                           '.*Comparison.*','.*Frequently(\s)*Asked(\s)*Questions.*');

  if (any { $sec_title =~ m/$_/sxm } @concepts_strings ) {
    $is_intro = q(1);
  }
  undef @concepts_strings;
  if ($is_intro ne q(1) &&
        (
        $sec_title =~ /How(\s)+.*/sxm
        && uc ($sec_title) !~ /HOW(\s)*DO(\s)*.*/sxm
        && uc ($sec_title) !~ /HOW(\s)*TO(\s)*.*/sxm
        )
  ){
    $is_intro = q(1);
  }
  if ($is_intro ne q(1)
      && $book_title =~ m/.*Concepts.*/sxm
      && $book_title !~ m/.*Concepts(\s)and(\s)Administration.*/sxm
      ) {
    $is_intro = q(1);
  }
  if ($is_intro ne q(1)
      && (
        $book_title =~ m/.*Overview.*/sxm
        || $book_title =~ m/.*New(\s)Features.*/sxm
         )
  ){
    $is_intro = q(1);
  }
  if ($is_intro eq q(0)) {return q(0);}

  return q(1);

}

##############################################################################
#
# Function: is_example
#
# Parameter: sec_title, book_name, fname_type
# Determines if the topic is of type example
# Rules:                   section_title like '%Example%'
#			or section_title like '%Sample%'
#			or section_title like '%Demo%'
#			or section_title like '%Scenario%'
#
#
##############################################################################

sub is_example {
   my $sec_title = shift;
   my $is_example = q(0);
   my @example_strings = ('.*Examples.*', '.*Sample.*', '.*Demo.*', '.*Scenario.*');

  if (any { $sec_title =~ m/$_/sxm } @example_strings ) {
    $is_example = q(1);
  }
  undef @example_strings;
  return $is_example;

}

##############################################################################
#
# Function: is_error_msg
#
# Parameter: sec_title
# Determines if the topic is of type error message
# Rules:
#                       section_title like '%Debug%'
#			or section_title like '%Diagnos%'
#			or section_title like '%Trouble%'
#			or section_title like '%Conflict%'
#			or section_title like '%Deadlock%'
#			or section_title like '%Problem%'
#			or section_title like '%Error%'
#			or section_title like '%Avoiding%'
#			or section_title like '%Failure%'
#			or section_title like '%Restriction%'
#			or (section_title like '%Limit%' and section_title not like '%Delimit%')
#			or section_title like '%Dump%'
#			or section_title like '%Emergency%'
#			or section_title like '%Test%'
#			or section_title like '%Exception%'
#			or booktitle like '%Performance%'
#			or booktitle like '%Tuning%'
#			or booktitle like '%Error%'
#			or booktitle like '%Messages%'
#
#
##############################################################################

sub is_error_message {
   my $sec_title  = shift;
   my $book_title = shift;
   my $is_error = q(0);
   my @error_strings = ('.*Debug.*', '.*Diagnos.*', '.*Trouble.*', '.*Conflict.*', '.*Deadlock.*',
                        '.*Problem.*', '.*Error.*', '.*Avoiding.*', '.*Failure.*', '.*Restriction.*',
                        '.*Dump.*', '.*Emergency.*', '.*Test.*', '.*Exception.*', '.*Performance.*',
                        '.*Tuning.*', '.*Error.*', '.*Messages.*');
   my @error_book_strings = ('.*Performance.*', '.*Tuning.*', '.*Error.*', '.*Messages.*');

  if (any { $sec_title =~ m/$_/sxm } @error_strings ) {
    $is_error = q(1);
  }
  if ($sec_title =~ m/Limit/sxm && $sec_title !~ m/Delimit/sxm) {
    $is_error = q(1);
  }
  if ((any { $book_title =~ m/$_/sxm } @error_book_strings) ) {
    $is_error = q(1);
  }
  undef @error_book_strings;
  undef @error_strings;
  return $is_error;
}

##############################################################################
#
# Function: is_faq
#
# Parameter: sec_title
# Determines if the topic is of type faq
#
##############################################################################

sub is_faq {
   my $sec_title = shift;
   my $is_faq = q(0);
   my @faq_strings = ('.*Frequently(\s)*Asked.*', '.*FAQ.*');

  if (any { $sec_title =~ m/$_/sxm } @faq_strings ) {
    $is_faq = q(1);
  }
  undef @faq_strings;
  return $is_faq;

}


##############################################################################
#
# Function: is_tasks
#
# Parameter: sec_title
# Determines if the topic is of type task
##############################################################################

sub is_tasks {

    my $sec_title = shift;
    my $is_tasks  = q(0);
    my @not_tasks_word = ('^STRING(\s).*', '^Listing _f(\s).*', '^Incoming(\s).*', '^Outgoing(\s).*', '^Operating(\s)*System.*', '^Networking.*');
    my @tasks_word = ('^HOW(\s)DO(\s).*', '^HOW(\s)TO(\s).*' ,'.*TUTORIAL.*');

    # first word with ing
    if ($sec_title =~ m/^([a-zA-Z]+)ing(\s)+(.*)/sxm) {
      $is_tasks  = q(1);
    }

    # and substr(section_title,1,1) between 'A' and 'Z'
    if ($sec_title !~ m/^[A-Z]+(.*)/sxm) {
      $is_tasks  = q(0);
    }

    if (any { $sec_title =~ m/$_/sxm } @not_tasks_word ) {
      $is_tasks = q(0);
    }
    if (any { $sec_title =~ m/$_/isxm } @tasks_word ) {
      $is_tasks = q(1);
    }
    undef @not_tasks_word;
    undef @tasks_word;
    return $is_tasks;
}

##############################################################################
#
# Function: is_references
#
# Parameter: book_title
# Determines if the topic is of type references
##############################################################################

sub is_references {
    my $booktitle = shift;
    my $sec_title = shift;
    
    my $is_reference = q(0);
    my @list_of_ref_titles = ('Concepts','Administrator'."'".'s Guide','SQL Reference',
                              'SQL Language Reference','Reference',
                              'PL/SQL User'."'".'s Guide and Reference','Performance Tuning Guide and Reference',
                              'Performance Tuning Guide','Application Developer'."'".'s Guide - Fundamentals',
                              '2 Day DBA');
    if (any { $booktitle =~ m/$_/ } @list_of_ref_titles ) {
      $is_reference = q(1);
    }
    if ($sec_title eq uc $sec_title) {
      $is_reference = q(1);
    }
    undef @list_of_ref_titles;
    return $is_reference;
}

##############################################################################
#
# Function: is_glossary
#
# Parameter: topic_class
# Determines if the topic is of type glossary
##############################################################################

sub is_glossary {
  my $topic_class = shift;
  if ($topic_class eq q(glossterm) || $topic_class eq q(glossary) || $topic_class eq q(glossentry)) {
     return q(1);
  }
  return q(0);
}

##############################################################################
#
# Function: is_chapter
#
# Parameter: topic_class
# Determines if the topic is of type chapter
##############################################################################

sub is_chapter {
  my $topic_class = shift;
  if (lc $topic_class eq q(chapter) ) {
     return q(1);
  }
  return q(0);
}

##############################################################################
#
# Function: roles
#
# Parameter: path, book_title
# Determines if the topic is of type glossary
##############################################################################

sub roles {
  my $pathv      = shift;
  my $book_title = shift;
  my $type_pn    = shift;
  my $type_path  = shift;
  my $roles = q();

  if ($book_title =~ m/user/sxmi) {
     $roles .= ",user";
  }
  elsif (any { $type_pn =~ m/$_/sxmi } @user_pns ) {
     $roles .= ",user";
  }

  if (   $pathv =~ m/.*appdev[.].*/sxm
      || $pathv =~ m/.*dev[.].*/sxm
      || $pathv =~ m/.*java[.].*/sxm
      || $book_title =~ m/.*Developer's.*/sxm
      || $book_title =~ m/.*(\s)+API(\s)+.*/sxm
      || $book_title =~ m/.*Javadoc.*/sxm

  ) {
     $roles .= ",developer";
  }
  elsif (any { $type_pn =~ m/$_/sxmi } @developer_pns ) {
     $roles .= ",developer";
  }


  if (   $pathv =~ m/.*server[.].*/sxm
      || $pathv =~ m/.*em[.].*/sxm
      || $pathv =~ m/.*admin[.].*/sxm
      || $book_title =~ m/.*Administrat.*/sxm
      || $book_title =~ m/.*2(\s)+Day(\s)+DBA.*/sxm

  ) {
     $roles .= ",administrator";
  }
  elsif (any { $type_pn =~ m/$_/sxmi } @administrator_pns ) {
     $roles .= ",administrator";
  }

  $roles =~ s/^,//sxm;
  return $roles;
}

sub elastic_search_mapping {
    my $mapping_type = shift;
    $mapping_type =~ s/_(.*)//sxm;
    $mapping_type =~ s/-(.*)//sxm;
    if ( $mapping_type =~ m/([[:alpha:]](\d){5}([_-](\d){1,2})*)\//sxm ) {
       $mapping_type = lc $mapping_type;
    }
    if (exists $index_type_mappings{$mapping_type}) {
      return;
    }
    my $elastic_search_mapping = <<"TOP";
curl -sS -XPUT 'http://${server_elastic_search}:9200/${context}/${mapping_type}/_mapping' -d '
{
    "${mapping_type}" : {
        "properties" : {
            "id" : {"type" : "string", "index" : "not_analyzed"},
            "title" : {"type" : "string"},
            "summary" : {"type" : "string"},
            "book_title" : {"type" : "string"},
            "part_number" : {"type" : "string", "index" : "not_analyzed"},
            "book_release" : {"type" : "string"},
            "ul" : {"type" : "string"},
            "book_url" : {"type" : "string"},
            "topic_type" : {"type" : "string"},
            "roles" : {"type" : "string"},
            "lang" : {"type" : "string"},
            "page_title" : {"type" : "string"},
            "release_date" : {"type" : "date", "format" : "yyyy-mm-dd" },
            "formats" : {"type" : "string"},
            "libraryurl" : {"type" : "string", "index" : "not_analyzed"},
            "url" : {"type" : "string", "index" : "not_analyzed"},
            "description" : {"type" : "string"},
            "mainpn" : {"type" : "string", "index" : "not_analyzed"},
            "librarypn" : {"type" : "string", "index" : "not_analyzed"},
            "category_name" : {"type" : "string", "index" : "not_analyzed"},
            "release_number" : {"type" : "string", "index" : "not_analyzed"},
            "computedtype" : {"type" : "string"},
            "keywords" : {"type" : "string"}
        }
    }
}
'
TOP
    $index_type_mappings{$mapping_type} = q();

    open my $CHUNK, '>>', $jsonoutputfolder . q(/) . $library_partnumber . q(-mapping.txt)
        or croak "Couldnt write to json output mapping file: $OS_ERROR\n";
    binmode $CHUNK, ':encoding(UTF-8)';
    print {$CHUNK} $elastic_search_mapping . "\n\n";
    print {$CHUNK} q(VIVEK-SAMPLE) . "\n\n";
    close $CHUNK
        or carp "Cant close: $OS_ERROR";

  return;

}

sub get_correct_date_format {
  my $raw_date = shift;
  $raw_date =~ s/\s(.*)//gis;
  $raw_date =~ s/T(.*)//gis;
  my $reldate = "";
  if ($raw_date =~ m/[0-9]{4}[-|\/][0-9]{1,2}[-|\/][0-9]{1,2}/) {
    $raw_date =~ s/\//-/gis;
    my @date_parts = split (/-/, $raw_date);
    if (scalar @date_parts == 3) {
        if (length $date_parts[1] < 2) {
           # its a month
           $date_parts[1] = "0".$date_parts[1];
        }
        if (length $date_parts[2] < 2) {
           # its a month
           $date_parts[2] = "0".$date_parts[2];
        }
        $reldate = $date_parts[0]."-".$date_parts[1]."-".$date_parts[2];
    }
  }
  return $reldate;
}

sub snapshot_time {
   (my $sec, my $min, my $hour, my $mday, my $mon, my $year, my $wday, my $yday, my $isdst) = gmtime();
   $mon=$mon+1; $year = 1900+$year;
   if($sec<10){
      $sec = "0".$sec;
   }
   if($min<10){
      $min = "0".$min;
   }
   if($hour<10){
      $hour = "0".$hour;
   }
   if($mon<10){
      $mon = "0".$mon;
   }

   my $todays_date = "DATE_".$year."_".$mon."_".$mday."_TIME_".$hour."_".$min."_".$sec;
   return($todays_date);

}

sub calculate_path {
   my $folderfrom = shift;
   my $fileto = shift;
   my $pcomputed = File::Spec->catfile($folderfrom, $fileto);
   if (-f $pcomputed) {
     $pcomputed = abs_path($pcomputed);
     $pcomputed = File::Spec->abs2rel($pcomputed);
   }
   else{
      $pcomputed = q();
   }
   return $pcomputed;
}

sub tidyhtml {
    my $rawfile = shift;
    if (-f "c:\\dev5\\src\\tools\\tidy.exe") {
      system ("c:\\dev5\\src\\tools\\tidy.exe -q  -raw -o ".$rawfile." -wrap 0 -ashtml -quiet --show-warnings no --show-errors 0 --preserve-entities y --tidy-mark 0 ".$rawfile);
    }
    else {
      system ("/usr/bin/tidy -q -raw -o ".$rawfile." -wrap 0 -ashtml -quiet --show-warnings no --show-errors 0 --preserve-entities y --tidy-mark 0 ".$rawfile);
    }
    return ;
}

sub encode_entities_html {
   my $string = shift;
   #return HTML::Entities::encode_entities($string);
   return $string;
}

sub getFolderMappings {
        my $mainPN = shift;
        $mainPN =~ s/_/-/gis;
        $mainPN = uc ($mainPN);
        my $url = 'http://pdb-stage.us.oracle.com/subFolderMappings.jsp?pn='.$mainPN;
        my $summaries4perl = '';

        my $ua = new LWP::UserAgent();
        my $resp = $ua->get($url);
        if ( $resp->is_success() ) {
            $summaries4perl = $resp->content();
        }

        $summaries4perl = Encode::decode('UTF-8', $summaries4perl);
        eval $summaries4perl;
        if ( $@ ) {
            print $@;
            %subfolder_mappings = ();
        }
}

sub standardize_release_number {
   my $rn = shift;
   if (length $rn < 1) {
     $rn = "0";
   }
   my $numberOfDotPlaces = 5;
   $rn =~ s/^[.]//gis;
   $rn =~ s/[.]$//gis;

   my @parts = split(/\./, $rn);
   for (my $dots = 0; $dots < ($numberOfDotPlaces - scalar @parts); $dots++) {
     $rn .= ".0";
   }
   return $rn;
}

sub checkfilesimilarity {
  my $indexfiledetected = shift;
  my $tocinthisfolder = $indexfiledetected;
  $tocinthisfolder =~ s/(.*)\/(.*)/$1/gis;
  $tocinthisfolder = $tocinthisfolder."/toc.htm";
  if (compare($tocinthisfolder,$indexfiledetected) == 0) {
     return 1;
  }
  else {
    return 0;
  }
}

sub properly_decode {
    my $filejoined_content = shift;
    if (   $filejoined_content =~ m{ <[?]xml [^>]+ encoding [[:space:]]* = [[:space:]]* ['"] utf -? 8 }xmsi
        || $filejoined_content =~ m{ <meta [^>]+ charset [[:space:]]* = [[:space:]]* utf -? 8 }xmsi )
    {
        ##print "DEBUG:: : At 1\n";
        $filejoined_content = Encode::decode( 'utf8', $filejoined_content );
    }
    elsif (   $filejoined_content =~ m{ <[?]xml [^>]+ encoding [[:space:]]* = [[:space:]]* ['"] (.*?) ['"]}xmsi ) {
        my $charencodingfound = $1;
        ##print "DEBUG:: : At 2:".$charencodingfound."\n";
        $charencodingfound =~ s/^(\s)+//gis;
        $charencodingfound =~ s/(\s)+$//gis;
        if (exists $all_encoding{lc($charencodingfound)}) {
          Encode::from_to ($filejoined_content,$charencodingfound, "utf8");
          $filejoined_content = Encode::decode( "utf8", $filejoined_content );
        }
    }
    elsif (   $filejoined_content =~ m{ <meta [^>]+ charset [[:space:]]* = [[:space:]]* ['"] (.*?) ['"] }xmsi ) {
        my $charencodingfound = $1;
        ##print "DEBUG:: : At 3:".$charencodingfound."\n";
        $charencodingfound =~ s/^(\s)+//gis;
        $charencodingfound =~ s/(\s)+$//gis;
        if (exists $all_encoding{lc($charencodingfound)}) {
          Encode::from_to ($filejoined_content,$charencodingfound, "utf8");
          $filejoined_content = Encode::decode( "utf8", $filejoined_content );
        }
    }
    elsif (   $filejoined_content =~ m{ <meta [^>]+ charset [[:space:]]* = [[:space:]]* ([^"]+) ["] }xmsi ) {
        my $charencodingfound = $1;
        ##print "DEBUG:: : At 4:".$charencodingfound."\n";
        $charencodingfound =~ s/^(\s)+//gis;
        $charencodingfound =~ s/(\s)+$//gis;
        if (exists $all_encoding{lc($charencodingfound)}) {
          Encode::from_to ($filejoined_content,$charencodingfound, "utf8");
          $filejoined_content = Encode::decode( "utf8", $filejoined_content );
        }
    }
    elsif (   $filejoined_content =~ m{ <meta [^>]+ charset [[:space:]]* = [[:space:]]* ([^']+) ['] }xmsi ) {
        my $charencodingfound = $1;
        ##print "DEBUG:: : At 5:".$charencodingfound."\n";
        $charencodingfound =~ s/^(\s)+//gis;
        $charencodingfound =~ s/(\s)+$//gis;
        if (exists $all_encoding{lc($charencodingfound)}) {
          Encode::from_to ($filejoined_content,$charencodingfound, "utf8");
          $filejoined_content = Encode::decode( "utf8", $filejoined_content );
        }
    }
    return $filejoined_content;
}

sub get_encoding_list {
  # utf-8
  $all_encoding{'unicode-1-1-utf-8'} = "utf-8";
  $all_encoding{'utf-8'} = "utf-8";
  $all_encoding{'utf8'} = "utf-8";

  # ibm866
  $all_encoding{'866'} = "ibm866";
  $all_encoding{'cp866'} = "ibm866";
  $all_encoding{'csibm866'} = "ibm866";
  $all_encoding{'ibm866'} = "ibm866";

  # iso-8859-2
  $all_encoding{'csisolatin2'} = "iso-8859-2";
  $all_encoding{'iso-8859-2'} = "iso-8859-2";
  $all_encoding{'iso-ir-101'} = "iso-8859-2";
  $all_encoding{'iso8859-2'} = "iso-8859-2";
  $all_encoding{'iso88592'} = "iso-8859-2";
  $all_encoding{'iso_8859-2'} = "iso-8859-2";
  $all_encoding{'iso_8859-2:1987'} = "iso-8859-2";
  $all_encoding{'l2'} = "iso-8859-2";
  $all_encoding{'latin2'} = "iso-8859-2";

  # iso-8859-3
  $all_encoding{'csisolatin3'} = "iso-8859-3";
  $all_encoding{'iso-8859-3'} = "iso-8859-3";
  $all_encoding{'iso-ir-109'} = "iso-8859-3";
  $all_encoding{'iso8859-3'} = "iso-8859-3";
  $all_encoding{'iso88593'} = "iso-8859-3";
  $all_encoding{'iso_8859-3'} = "iso-8859-3";
  $all_encoding{'iso_8859-3:1988'} = "iso-8859-3";
  $all_encoding{'l3'} = "iso-8859-3";
  $all_encoding{'latin3'} = "iso-8859-3";;

  # iso-8859-4
  $all_encoding{'csisolatin4'} = 'iso-8859-4';
  $all_encoding{'iso-8859-4'} = 'iso-8859-4';
  $all_encoding{'iso-ir-110'} = 'iso-8859-4';
  $all_encoding{'iso8859-4'} = 'iso-8859-4';
  $all_encoding{'iso88594'} = 'iso-8859-4';
  $all_encoding{'iso_8859-4'} = 'iso-8859-4';
  $all_encoding{'iso_8859-4:1988'} = 'iso-8859-4';
  $all_encoding{'l4'} = 'iso-8859-4';
  $all_encoding{'latin4'} = 'iso-8859-4';

  # iso-8859-5
  $all_encoding{'csisolatincyrillic'} = 'iso-8859-5';
  $all_encoding{'cyrillic'} = 'iso-8859-5';
  $all_encoding{'iso-8859-5'} = 'iso-8859-5';
  $all_encoding{'iso-ir-144'} = 'iso-8859-5';
  $all_encoding{'iso8859-5'} = 'iso-8859-5';
  $all_encoding{'iso88595'} = 'iso-8859-5';
  $all_encoding{'iso_8859-5'} = 'iso-8859-5';
  $all_encoding{'iso_8859-5:1988'} = 'iso-8859-5';

  # iso-8859-6
  $all_encoding{'arabic'} = 'iso-8859-6';
  $all_encoding{'asmo-708'} = 'iso-8859-6';
  $all_encoding{'csiso88596e'} = 'iso-8859-6';
  $all_encoding{'csiso88596i'} = 'iso-8859-6';
  $all_encoding{'csisolatinarabic'} = 'iso-8859-6';
  $all_encoding{'ecma-114'} = 'iso-8859-6';
  $all_encoding{'iso-8859-6'} = 'iso-8859-6';
  $all_encoding{'iso-8859-6-e'} = 'iso-8859-6';
  $all_encoding{'iso-8859-6-i'} = 'iso-8859-6';
  $all_encoding{'iso-ir-127'} = 'iso-8859-6';
  $all_encoding{'iso8859-6'} = 'iso-8859-6';
  $all_encoding{'iso88596'} = 'iso-8859-6';
  $all_encoding{'iso_8859-6'} = 'iso-8859-6';
  $all_encoding{'iso_8859-6:1987'} = 'iso-8859-6';

  # iso-8859-7
  $all_encoding{'csisolatingreek'} = 'iso-8859-7';
  $all_encoding{'ecma-118'} = 'iso-8859-7';
  $all_encoding{'elot_928'} = 'iso-8859-7';
  $all_encoding{'greek'} = 'iso-8859-7';
  $all_encoding{'greek8'} = 'iso-8859-7';
  $all_encoding{'iso-8859-7'} = 'iso-8859-7';
  $all_encoding{'iso-ir-126'} = 'iso-8859-7';
  $all_encoding{'iso8859-7'} = 'iso-8859-7';
  $all_encoding{'iso88597'} = 'iso-8859-7';
  $all_encoding{'iso_8859-7'} = 'iso-8859-7';
  $all_encoding{'iso_8859-7:1987'} = 'iso-8859-7';
  $all_encoding{'sun_eu_greek'} = 'iso-8859-7';

  # iso-8859-8
  $all_encoding{'csiso88598e'} = 'iso-8859-8';
  $all_encoding{'csisolatinhebrew'} = 'iso-8859-8';
  $all_encoding{'hebrew'} = 'iso-8859-8';
  $all_encoding{'iso-8859-8'} = 'iso-8859-8';
  $all_encoding{'iso-8859-8-e'} = 'iso-8859-8';
  $all_encoding{'iso-ir-138'} = 'iso-8859-8';
  $all_encoding{'iso8859-8'} = 'iso-8859-8';
  $all_encoding{'iso88598'} = 'iso-8859-8';
  $all_encoding{'iso_8859-8'} = 'iso-8859-8';
  $all_encoding{'iso_8859-8:1988'} = 'iso-8859-8';
  $all_encoding{'visual'} = 'iso-8859-8';

  # iso-8859-8-i
  $all_encoding{'csiso88598i'} = 'iso-8859-8-i';
  $all_encoding{'iso-8859-8-i'} = 'iso-8859-8-i';
  $all_encoding{'logical'} = 'iso-8859-8-i';

  # iso-8859-10
  $all_encoding{'csisolatin6'} = 'iso-8859-10';
  $all_encoding{'iso-8859-10'} = 'iso-8859-10';
  $all_encoding{'iso-ir-157'} = 'iso-8859-10';
  $all_encoding{'iso8859-10'} = 'iso-8859-10';
  $all_encoding{'iso885910'} = 'iso-8859-10';
  $all_encoding{'l6'} = 'iso-8859-10';
  $all_encoding{'latin6'} = 'iso-8859-10';

  # iso-8859-13
  $all_encoding{'iso-8859-13'} = 'iso-8859-13';
  $all_encoding{'iso8859-13'} = 'iso-8859-13';
  $all_encoding{'iso885913'} = 'iso-8859-13';

  # iso-8859-14
  $all_encoding{'iso-8859-14'} = 'iso-8859-14';
  $all_encoding{'iso8859-14'} = 'iso-8859-14';
  $all_encoding{'iso885914'} = 'iso-8859-14';

  # iso-8859-15
  $all_encoding{'csisolatin9'} = 'iso-8859-15';
  $all_encoding{'iso-8859-15'} = 'iso-8859-15';
  $all_encoding{'iso8859-15'} = 'iso-8859-15';
  $all_encoding{'iso885915'} = 'iso-8859-15';
  $all_encoding{'iso_8859-15'} = 'iso-8859-15';
  $all_encoding{'l9'} = 'iso-8859-15';

  # iso-8859-16
  $all_encoding{'iso-8859-16'} = 'iso-8859-16';

  # koi8-r
  $all_encoding{'cskoi8r'} = 'koi8-r';
  $all_encoding{'koi'} = 'koi8-r';
  $all_encoding{'koi8'} = 'koi8-r';
  $all_encoding{'koi8-r'} = 'koi8-r';
  $all_encoding{'koi8_r'} = 'koi8-r';

  # koi8-u
  $all_encoding{'koi8-u'} = 'koi8-u';

  # macintosh
  $all_encoding{'csmacintosh'} = 'macintosh';
  $all_encoding{'mac'} = 'macintosh';
  $all_encoding{'macintosh'} = 'macintosh';
  $all_encoding{'x-mac-roman'} = 'macintosh';

  # windows-874
  $all_encoding{'dos-874'} = 'windows-874';
  $all_encoding{'iso-8859-11'} = 'windows-874';
  $all_encoding{'iso8859-11'} = 'windows-874';
  $all_encoding{'iso885911'} = 'windows-874';
  $all_encoding{'tis-620'} = 'windows-874';
  $all_encoding{'windows-874'} = 'windows-874';

  # windows-1250
  $all_encoding{'cp1250'} = 'windows-1250';
  $all_encoding{'windows-1250'} = 'windows-1250';
  $all_encoding{'x-cp1250'} = 'windows-1250';

  # windows-1251
  $all_encoding{'cp1251'} = 'windows-1251';
  $all_encoding{'windows-1251'} = 'windows-1251';
  $all_encoding{'x-cp1251'} = 'windows-1251';

  # windows-1252
  $all_encoding{'ansi_x3.4-1968'} = 'windows-1252';
  $all_encoding{'ascii'} = 'windows-1252';
  $all_encoding{'cp1252'} = 'windows-1252';
  $all_encoding{'cp819'} = 'windows-1252';
  $all_encoding{'csisolatin1'} = 'windows-1252';
  $all_encoding{'ibm819'} = 'windows-1252';
  $all_encoding{'iso-8859-1'} = 'windows-1252';
  $all_encoding{'iso-ir-100'} = 'windows-1252';
  $all_encoding{'iso8859-1'} = 'windows-1252';
  $all_encoding{'iso88591'} = 'windows-1252';
  $all_encoding{'iso_8859-1'} = 'windows-1252';
  $all_encoding{'iso_8859-1:1987'} = 'windows-1252';
  $all_encoding{'l1'} = 'windows-1252';
  $all_encoding{'latin1'} = 'windows-1252';
  $all_encoding{'us-ascii'} = 'windows-1252';
  $all_encoding{'windows-1252'} = 'windows-1252';
  $all_encoding{'x-cp1252'} = 'windows-1252';

  # windows-1253
  $all_encoding{'cp1253'} = 'windows-1253';
  $all_encoding{'windows-1253'} = 'windows-1253';
  $all_encoding{'x-cp1253'} = 'windows-1253';

  # windows-1254
  $all_encoding{'cp1254'} = 'windows-1254';
  $all_encoding{'csisolatin5'} = 'windows-1254';
  $all_encoding{'iso-8859-9'} = 'windows-1254';
  $all_encoding{'iso-ir-148'} = 'windows-1254';
  $all_encoding{'iso8859-9'} = 'windows-1254';
  $all_encoding{'iso88599'} = 'windows-1254';
  $all_encoding{'iso_8859-9'} = 'windows-1254';
  $all_encoding{'iso_8859-9:1989'} = 'windows-1254';
  $all_encoding{'l5'} = 'windows-1254';
  $all_encoding{'latin5'} = 'windows-1254';
  $all_encoding{'windows-1254'} = 'windows-1254';
  $all_encoding{'x-cp1254'} = 'windows-1254';

  # windows-1255
  $all_encoding{'cp1255'} = 'windows-1255';
  $all_encoding{'windows-1255'} = 'windows-1255';
  $all_encoding{'x-cp1255'} = 'windows-1255';

  # windows-1256
  $all_encoding{'cp1256'} = 'windows-1256';
  $all_encoding{'windows-1256'} = 'windows-1256';
  $all_encoding{'x-cp1256'} = 'windows-1256';

  # windows-1257
  $all_encoding{'cp1257'} = 'windows-1257';
  $all_encoding{'windows-1257'} = 'windows-1257';
  $all_encoding{'x-cp1257'} = 'windows-1257';

  # windows-1258
  $all_encoding{'cp1258'} = 'windows-1258';
  $all_encoding{'windows-1258'} = 'windows-1258';
  $all_encoding{'x-cp1258'} = 'windows-1258';

  # x-mac-cyrillic
  $all_encoding{'x-mac-cyrillic'} = 'x-mac-cyrillic';
  $all_encoding{'x-mac-ukrainian'} = 'x-mac-cyrillic';

  # gb18030
  $all_encoding{'chinese'} = 'gb18030';
  $all_encoding{'csgb2312'} = 'gb18030';
  $all_encoding{'csiso58gb231280'} = 'gb18030';
  $all_encoding{'gb18030'} = 'gb18030';
  $all_encoding{'gb2312'} = 'gb18030';
  $all_encoding{'gb_2312'} = 'gb18030';
  $all_encoding{'gb_2312-80'} = 'gb18030';
  $all_encoding{'gbk'} = 'gb18030';
  $all_encoding{'iso-ir-58'} = 'gb18030';
  $all_encoding{'x-gbk'} = 'gb18030';

  # hz-gb-2312
  $all_encoding{'hz-gb-2312'} = 'hz-gb-2312';

  # big5
  $all_encoding{'big5'} = 'big5';
  $all_encoding{'big5-hkscs'} = 'big5';
  $all_encoding{'cn-big5'} = 'big5';
  $all_encoding{'csbig5'} = 'big5';
  $all_encoding{'x-x-big5'} = 'big5';

  # euc-jp
  $all_encoding{'cseucpkdfmtjapanese'} = 'euc-jp';
  $all_encoding{'euc-jp'} = 'euc-jp';
  $all_encoding{'x-euc-jp'} = 'euc-jp';

  # iso-2022-jp
  $all_encoding{'csiso2022jp'} = 'iso-2022-jp';
  $all_encoding{'iso-2022-jp'} = 'iso-2022-jp';

  # shift_jis
  $all_encoding{'csshiftjis'} = 'shift_jis';
  $all_encoding{'ms_kanji'} = 'shift_jis';
  $all_encoding{'shift-jis'} = 'shift_jis';
  $all_encoding{'shift_jis'} = 'shift_jis';
  $all_encoding{'sjis'} = 'shift_jis';
  $all_encoding{'windows-31j'} = 'shift_jis';
  $all_encoding{'x-sjis'} = 'shift_jis';

  # euc-kr
  $all_encoding{'cseuckr'} = 'euc-kr';
  $all_encoding{'csksc56011987'} = 'euc-kr';
  $all_encoding{'euc-kr'} = 'euc-kr';
  $all_encoding{'iso-ir-149'} = 'euc-kr';
  $all_encoding{'korean'} = 'euc-kr';
  $all_encoding{'ks_c_5601-1987'} = 'euc-kr';
  $all_encoding{'ks_c_5601-1989'} = 'euc-kr';
  $all_encoding{'ksc5601'} = 'euc-kr';
  $all_encoding{'ksc_5601'} = 'euc-kr';
  $all_encoding{'windows-949'} = 'euc-kr';

  # replacement
  $all_encoding{'csiso2022kr'} = 'replacement';
  $all_encoding{'iso-2022-cn'} = 'replacement';
  $all_encoding{'iso-2022-cn-ext'} = 'replacement';
  $all_encoding{'iso-2022-kr'} = 'replacement';

  # utf-16be
  $all_encoding{'utf-16be'} = 'utf-16be';

  # utf-16le
  $all_encoding{'utf-16'} = 'utf-16le';
  $all_encoding{'utf-16le'} = 'utf-16le';

  # x-user-defined
  $all_encoding{'x-user-defined'} = 'x-user-defined';
}

sub trim {
  my $msg = shift;
  if (! $$msg || length $$msg < 1) {
    return "";
  }
  $$msg =~ s/\r//gis;
  $$msg =~ s/\n//gis;  
  $$msg =~ s/^(\s)+//gis;  
  $$msg =~ s/(\s)+$//gis;  
}

sub extractids {
    my $text_backup = shift;
    my $idstream = HTML::TokeParser->new( \$$text_backup )
        or carp "Couldn't parse: $OS_ERROR";
    while ( my $idtoken = $idstream->get_token() ) {
        if (   ( $idtoken->[0] eq 'S' && $idtoken->[1] eq 'a' )
            || ( $idtoken->[2]{'id'} && length $idtoken->[2]{'id'} > 0 ) )
        {
            my $secid   = $idtoken->[2]{'id'};
            my $secname = $idtoken->[2]{'name'};

            if ( $secname && length $secname > 0 ) {
                $secid = $secname;
            }
            if ( $secid && length $secid > 0 ) {
                push @extract_ids, $secid;
            }
        }
    }
    return @extract_ids;
}

sub jsontitle {
  my $str = shift;
  if ($str && length $str >= 100) {
    $str =~ s/\((\s)*//gis;
    $str =~ s/(\s)*\)//gis;
    $str =~ s/\[(\s)*//gis;
    $str =~ s/(\s)*\]//gis;
    $str =~ s/\}(\s)*//gis;
    $str =~ s/(\s)*\}//gis;
  }
  return $str;
}

__END__

=head1 NAME

analyzer_elastic_json.pl - Generates the JSON data file

=head1 USAGE

 analyzer_elastic_json.pl -f ./ -l E11882-091 --ctx db112

=head1 DESCRIPTION

Scans a directory of HTML, writes the JSON data file for elastic search.

=head1 REQUIRED ARGUMENTS

none

=head1 OPTIONS

=over 4

=item -f --folder

The directory where the HTML files for which the JSOPN data
is to be created is present.

=item -l --lib

The library part number

=item -c --ctx

The library context value.

=item -p --prod

The product shortname using which the index will be created.

=back

=head1 EXAMPLES

  analyzer_elastic_json.pl -f ./ -l E11882-091 --ctx db112
 

=head1 DIAGNOSTICS

n/a

=head1 EXIT STATUS

n/a

=head1 CONFIGURATION

n/a

=head1 DEPENDENCIES

n/a

=head1 INCOMPATIBILITIES

n/a

=head1 BUGS AND LIMITATIONS

n/a

=head1 AUTHOR

Vivek Kumar <vivek.kumar@oracle.com>

=head1 LICENSE AND COPYRIGHT

Copyright 2014, Oracle and/or its affiliates. All rights reserved.
