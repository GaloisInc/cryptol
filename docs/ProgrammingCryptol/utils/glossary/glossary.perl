# File        : glossary.perl
# Author      : Nicola Talbot
# Date        : 5 December 2005
# Version     : 1.03
# Description : LaTeX2HTML implementation of glossary package.

package main;

# These are the only package options implemented.

sub do_glossary_style_altlist{
}

sub do_glossary_style_hyper{
}

sub do_glossary_style_hyper_true{
}

sub do_glossary_style_hyperacronym{
}

sub do_glossary_style_hyperacronym_true{
}

sub do_glossary_toc{
}

sub do_glossary_toc_true{
}

$acronymtype = 'glossary';

sub do_glossary_acronym{
   &do_glossary_acronym_true
}

sub do_glossary_acronym_true{
   $gls_mark{'acronym'} = "<tex2html_acronym_mark>";
   $gls_file_mark{'acronym'} = "<tex2html_acronym_file_mark>";
   $gls_title{'acronym'} = "\\acronymname";
   $delimN{'acronym'} = ", ";
   $glodelim{'acronym'} = " ";
   $glsnumformat{'acronym'} = "textrm";
   $acronymtype = 'acronym';
}

sub do_glossary_acronym_false{
   $acronymtype = 'glossary';
}

sub do_cmd_acronymname{
   join('', 'List of Acronyms', $_[0]);
}

# modify set_depth_levels so that glossary is added

$gls_mark{'glossary'} = "<tex2html_gls_mark>";
$gls_file_mark{'glossary'} = "<tex2html_gls_file_mark>";
$gls_title{'glossary'} = "Glossary";
$delimN{'glossary'} = ", ";
$glodelim{'glossary'} = " ";
$glsnumformat{'glossary'} = "textrm";

sub replace_glossary_markers{
   foreach $type (keys %gls_mark)
   {
      if (defined &add_gls_hook)
        {&add_gls_hook if (/$gls_mark{$type}/);}
      else
        {&add_gls($type) if (/$gls_mark{$type}/);}

      s/$gls_file_mark{$type}/$glsfile{$type}/g;
   }
}

# there must be a better way of doing this
# other than copying the orginal code and adding to it.
sub replace_general_markers {
    if (defined &replace_infopage_hook) {&replace_infopage_hook if (/$info_page_mark/);}
    else { &replace_infopage if (/$info_page_mark/); }
    if (defined &add_idx_hook) {&add_idx_hook if (/$idx_mark/);}
    else {&add_idx if (/$idx_mark/);}
    &replace_glossary_markers;

    if ($segment_figure_captions) {
s/$lof_mark/$segment_figure_captions/o
    } else { s/$lof_mark/$figure_captions/o }
    if ($segment_table_captions) {
s/$lot_mark/$segment_table_captions/o
    } else { s/$lot_mark/$table_captions/o }
    &replace_morelinks();
    if (defined &replace_citations_hook) {&replace_citations_hook if /$bbl_mark/;}
    else {&replace_bbl_marks if /$bbl_mark/;}
    if (defined &add_toc_hook) {&add_toc_hook if (/$toc_mark/);}
    else {&add_toc if (/$toc_mark/);}
    if (defined &add_childs_hook) {&add_childs_hook if (/$childlinks_on_mark/);}
    else {&add_childlinks if (/$childlinks_on_mark/);}
    &remove_child_marks;

    if (defined &replace_cross_references_hook) {&replace_cross_references_hook;}
    else {&replace_cross_ref_marks if /$cross_ref_mark||$cross_ref_visible_mark/;}
    if (defined &replace_external_references_hook) {&replace_external_references_hook;}
    else {&replace_external_ref_marks if /$external_ref_mark/;}
    if (defined &replace_cite_references_hook) {&replace_cite_references_hook;}
    else { &replace_cite_marks if /$cite_mark/; }
    if (defined &replace_user_references) {
  &replace_user_references if /$user_ref_mark/; }

}

sub add_gls{
    local($sidx_style, $eidx_style) =('<STRONG>','</STRONG>');
    if ($INDEX_STYLES) {
if ($INDEX_STYLES =~/,/) {
local(@styles) = split(/\s*,\s*/,$INDEX_STYLES);
    $sidx_style = join('','<', join('><',@styles) ,'>');
    $eidx_style = join('','</', join('></',reverse(@styles)) ,'>');
} else {
    $sidx_style = join('','<', $INDEX_STYLES,'>');
    $eidx_style = join('','</', $INDEX_STYLES,'>');
}
    }
    &add_real_gls
}

sub gloskeysort{
   local($x, $y) = ($a, $b);
   $x=~s/^(.*)###(\d+)$/\l\1/;
   local($x_id) = $2;
   $y=~s/^(.*)###(\d+)$/\l\1/;
   local($y_id) = $2;

   local($n) = ($x cmp $y);

   if ($n == 0)
   {
      $n = ($x_id <=> $y_id);
   }

   $n;
}

sub add_real_gls{
    local($type) = @_;
    print "\nDoing the $type ...";
    local($key, $str, @keys, $glossary, $level, $count,
  @previous, @current, $id, $linktext, $delimN);

    @keys = keys %{$glossary{$type}};

    @keys = sort gloskeysort @keys;

    $level = 0;

    $delimN = $delimN{$type};

    foreach $key (@keys) {
        $current = $key;
$str = $current;
$str =~ s/\#\#\#\d+$//o; # Remove the unique id's
        #$linktext = $cross_ref_visible_mark;
        $id = ++$global{'max_id'};
        $linktext = "\\$glossary_format{$type}{$key}${OP}$id${CP}$glossary_linktext{$type}{$key}${OP}$id${CP}";
        $linktext = &translate_commands($linktext);
$glossary .=
    # If it's the same string don't start a new line
    (&index_key_eq($current, $previous) ?
               $delimN
               . $glossary{$type}{$key}
               . $linktext
               . "</A>\n"
            : "<DT>"
                   . $glossary_name{$type}{$key}
                   . "<DD>". $glossary_desc{$type}{$key}
                   . $glodelim{$type} . $glossary{$type}{$key}
     . $linktext. "</A>\n");
$previous = $current;
    }
    $glossary = '<DD>'.$glossary unless ($glossary =~ /^\s*<D(T|D)>/);

    $glossary =~ s/(<A [^>]*>)(<D(T|D)>)/$2$1/g;

    $str = &translate_commands("\\glossarypostamble");
    s/$gls_mark{$type}/$preglossary\n<DL COMPACT>\n$glossary<\/DL>$str\n/s;
}

sub set_depth_levels {
    # Sets $outermost_level
    local($level);
    # scan the document body, not the preamble, for use of sectioning commands
    my ($contents) = $_;
    if ($contents =~ /\\begin\s*((?:$O|$OP)\d+(?:$C|$CP))document\1|\\startdocument/s) {
$contents = $';
    }
    foreach $level ("part", "chapter", "section", "subsection",
    "subsubsection", "paragraph") {
last if (($outermost_level) = $contents =~ /\\($level)$delimiter_rx/);
last if (($outermost_level) = $contents =~ /\\endsegment\s*\[\s*($level)\s*\]/s);
if ($contents =~ /\\segment\s*($O\d+$C)[^<]+\1\s*($O\d+$C)\s*($level)\s*\2/s)
{ $outermost_level = $3; last };
    }
    $level = ($outermost_level ? $section_commands{$outermost_level} :
      do {$outermost_level = 'section'; 3;});

    if ($REL_DEPTH && $MAX_SPLIT_DEPTH) {
$MAX_SPLIT_DEPTH = $level + $MAX_SPLIT_DEPTH;
    } elsif (!($MAX_SPLIT_DEPTH)) { $MAX_SPLIT_DEPTH = 1 };

    %unnumbered_section_commands = (
          'tableofcontents', $level
, 'listoffigures', $level
, 'listoftables', $level
, 'bibliography', $level
, 'textohtmlindex', $level
, 'textohtmlglossary', $level
        , %unnumbered_section_commands
        );

    %section_commands = (
  %unnumbered_section_commands
        , %section_commands
        );
}

sub add_bbl_and_idx_dummy_commands {
    local($id) = $global{'max_id'};

    s/([\\]begin\s*$O\d+$C\s*thebibliography)/$bbl_cnt++; $1/eg;
    ## if ($bbl_cnt == 1) {
s/([\\]begin\s*$O\d+$C\s*thebibliography)/$id++; "\\bibliography$O$id$C$O$id$C $1"/geo;
    #}
    $global{'max_id'} = $id;
    s/([\\]begin\s*$O\d+$C\s*theindex)/\\textohtmlindex $1/o;
    s/[\\]printindex/\\textohtmlindex /o;
    &add_gls_dummy_commands;
    &lib_add_bbl_and_idx_dummy_commands() if defined(&lib_add_bbl_and_idx_dummy_commands);
}

# this gets called before do_cmd_newglossarytype
# so currently only substitutes \\printglossary and \\printacronym
sub add_gls_dummy_commands{
   #foreach $type (keys %gls_mark)
   #{
   #   #$id = ++$global{'max_id'};
   #   s/[\\]print$type/\\textohtmlglossary[$type]/sg;
   #}

   s/[\\]printglossary/\\textohtmlglossary/sg;
   s/[\\]printacronym/\\textohtmlglossary[$acronymtype]/sg;
}

# This is modified from do_cmd_textohtmlindex

sub do_cmd_textohtmlglossary{
   local($_) = @_;

   local($type);

   $_[0]=~s/^\s*\[([^]]*)\]//;
   $type = $1;
   if ($type eq '') {$type = 'glossary';}

   unless (defined $gls_mark{$type})
   {
      &write_warnings("glossary type '$type' not implemented");
   }

   if (eval "(defined \&do_cmd_${type}name) ||\$new_command{\"${type}name\"}")
   {
      local($br_id)=++$global{'max_id'};
      $TITLE = &translate_environments("$O$br_id$C\\${type}name$O$br_id$C");
   }
   else
   { $TITLE = $gls_title{$type} }
   $toc_sec_title = $TITLE;
   $glsfile{$type} = $CURRENT_FILE;
   if (%glossary_labels) { &make_glossary_labels(); }
   if (($SHORT_INDEX) && (%glossary_segment))
   { &make_preglossary(); }
   else
   { $preglossary = &translate_commands("\\glossarypreamble"); }
   local $idx_head = $section_headings{'textohtmlindex'};
   local($heading) = join(''
        , &make_section_heading($TITLE, $idx_head)
        , $gls_mark{$type} );
   local($pre,$post) = &minimize_open_tags($heading);
   join('',"<BR>\n" , $pre, $_[0]);
}

sub make_glossary_labels {
    local($key, @keys);
    @keys = keys %glossary_labels;
    foreach $key (@keys) {
        if (($ref_files{$key}) && !($ref_files{$key} eq "$glsfile{'glossary'}")) {
            local($tmp) = $ref_files{$key};
            &write_warnings("\nmultiple label $key , target in $glsfile{'glossary'} masks $tmp ");
        }
        $ref_files{$key} .= $glsfile{'glossary'};
    }
}

sub make_preglossary{ &make_real_preglossary }
sub make_real_preglossary{
    local($key, @keys, $head, $body);
    $head = "<HR>\n<H4>Legend:</H4>\n<DL COMPACT>";
    @keys = keys %glossary_segment;
    foreach $key (@keys) {
        local($tmp) = "segment$key";
        $tmp = $ref_files{$tmp};
        $body .= "\n<DT>$key<DD>".&make_named_href('',$tmp,$glossary_segment{$key});
    }
    $preglossary = join('', $head, $body, "\n</DL>") if ($body);
}

sub do_cmd_glossary { &do_real_glossary(@_) }
sub do_real_glossary {
    local($_) = @_;
    local($br_id, $str);
    local($type) = "glossary";
    local($anchor);

    if (s/^\S*$OP(\d+)${CP}type=(.+)$OP\1$CP//)
    {
       $type = $2;
    }

    local($idx_option,$pat) = &get_next_optional_argument;

    $str = &missing_braces unless (
(s/$next_pair_pr_rx/($br_id, $str) = ($1, $2);''/eo)
||(s/$next_pair_rx/($br_id, $str) = ($1, $2);''/eo));

    # the maths gets processed before being passed
    # to do_cmd_glossary.  How can I do this
    # substitution before it gets converted to an image?
    $str=~s/\"\"/\"/gs;
    $str=~s/\"\|/\|/gs;
    $str=~s/\"@/@/gs;
    $str=~s/\"!/!/gs;

    $str=~s/;SPMquot;;SPMquot;/;SPMquot;/gs;
    $str=~s/;SPMquot;\|/\|/gs;
    $str=~s/;SPMquot;\@/\@/gs;
    $str=~s/;SPMquot;!/!/gs;

    $anchor = &make_glossary_entry($br_id,$str,$anchor_invisible_mark,$type);

    join('', $anchor, $_);
}

sub make_glossary_entry { &make_real_glossary_entry(@_) }
sub make_real_glossary_entry {
    local($br_id,$str,$text,$type) = @_;
    local($this_file) = $CURRENT_FILE;
    $TITLE = $saved_title if (($saved_title)&&(!($TITLE)||($TITLE eq $default_title)));
    #extract name, sort, description and format data from $str
    local($name,$sort,$description,$format);

    unless (($str=~/name\s*=\s*${OP}(\d+)${CP}(.+)${OP}\1${CP}\s*,?/s && ($name=$2)) ||
        ($str=~/name\s*=\s*([^,]+)\s*,?/s && ($name=$1)))
    {
       &write_warnings("can't determine name key from $str");
    }

    unless (($str=~/sort\s*=\s*${OP}(\d+)${CP}(.+)${OP}\1${CP}\s*,?/s && ($sort=$2)) ||
        ($str=~/sort\s*=\s*([^,]+)\s*,?/s && ($sort=$1)))
    {
       $sort = $name;
    }

    unless (($str=~/description\s*=\s*${OP}(\d+)${CP}(.+)${OP}\1${CP}\s*,?/s && ($description=$2)) ||
        ($str=~/description\s*=\s*([^,]+)\s*,?/s && ($description=$1)))
    {
       &write_warnings("can't determine description key from $str");
    }

    unless (($str=~/format\s*=\s*${OP}(\d+)${CP}(.+)${OP}\1${CP}\s*,?/s && ($format=$2)) ||
        ($str=~/format\s*=\s*([^,]+)\s*,?/s && ($format=$1)))
    {
       $format = "glsnumformat[$type]";
    }

    # Save the reference
    $str = "$sort$description###" . ++$global{'max_id'}; # Make unique
    # concatenate multiple spaces into a single space
    # otherwise keys won't sort properly
    $str=~s/\s+/ /gs;
    $glossary{$type}{$str} .= &make_half_href($this_file."#$br_id");
    $glossary_name{$type}{$str} = $name;
    $glossary_format{$type}{$str} = $format;
    $glossary_desc{$type}{$str} = $description;
    $glossary_linktext{$type}{$str} = $TITLE;
    "<A HREF=$gls_file_mark{$type}#tex2html$href_name NAME=\"$br_id\">$text<\/A>";
}

sub do_cmd_xglossary{
  local($_) = @_;
  local($entry,$text);
  local($type) = "glossary";

  if (s/^$OP(\d+)${CP}type=(.+)$OP\1$CP//)
  {
     $type = $2;
  }

  $entry = &missing_braces unless
            s/$next_pair_pr_rx/$entry=$2;''/eo;

  $text = &missing_braces unless
            s/$next_pair_pr_rx/$text=$2;''/eo;

  $entry=~s/\"\"/\"/gs;
  $entry=~s/\"\|/\|/gs;
  $entry=~s/\"\@/\@/gs;
  $entry=~s/\"!/!/gs;

  $entry=~s/;SPMquot;;SPMquot;/;SPMquot;/gs;
  $entry=~s/;SPMquot;\|/\|/gs;
  $entry=~s/;SPMquot;\@/\@/gs;
  $entry=~s/;SPMquot;!/!/gs;

  $br_id = ++$global{'max_id'};
  join('', &make_glossary_entry($br_id,$entry,$text,$type),
       $_);
}

sub do_cmd_newglossarytype{
   local($type,$out,$in);
   $type = &missing_braces unless
           ($_[0]=~s/$next_pair_pr_rx//o&&($type=$2));
   $out = &missing_braces unless
           ($_[0]=~s/$next_pair_pr_rx//o&&($out=$2));
   $in = &missing_braces unless
           ($_[0]=~s/$next_pair_pr_rx//o&&($in=$2));

   &make_newglossarytype($type);

   $_[0];
}

sub make_newglossarytype{
   local($type) = @_;

   eval ("sub do_cmd_make$type\{\}");

   $gls_mark{$type} = "<tex2html_${type}_mark>";
   $gls_file_mark{$type} = "<tex2html_${type}_file_mark>";
   $gls_title{$type} = "\\glossaryname";

   local($tmp) = 'sub do_cmd_' . $type. '{';
   $tmp .= 'local($id) = ++$global{\'max_id\'};';
   $tmp .= '"\\\\glossary$OP$id${CP}type=' . $type . '$OP$id$CP".$_[0];';
   $tmp .= '}';

   eval($tmp);

   $tmp = 'sub do_cmd_x' . $type. '{';
   $tmp .= 'local($id) = ++$global{\'max_id\'};';
   $tmp .= '"\\\\xglossary$OP$id${CP}type=' . $type . '$OP$id$CP".$_[0];';
   $tmp .= '}';

   eval($tmp);

   $tmp = 'sub do_cmd_print' . $type. '{';
   #$tmp .= 'local($id)=++$global{\'max_id\'};';
   $tmp .= '"\\\\textohtmlglossary[' . $type
        . ']" . $_[0]';
   $tmp .= '}';

   eval($tmp);

   $delimN{$type} = ", ";
   $glodelim{$type} = "";
   $glsnumformat{$type} = "";

}

sub do_cmd_gloshort{
  local($_) = @_;
  join('', "<tex2html_GLOSHORT_mark>", $_);
}

sub do_cmd_glolong{
  local($_) = @_;
  join('', "<tex2html_GLOLONG_mark>", $_);
}

$acronymnamefmt = "<tex2html_GLOLONG_mark> (<tex2html_GLOSHORT_mark>)";

sub do_cmd_setacronymnamefmt{
   local($_) = @_;

   $acronymnamefmt = &missing_braces unless
             s/$next_pair_pr_rx/$acronymnamefmt=$2;''/eo;

   $_;
}

sub do_cmd_acronymfont{
   local($_) = @_;
   local($text) = &missing_braces unless
                  s/$next_pair_pr_rx/$text=$2;''/eo;

   $text . $_;
}

 %acronym = ();

sub do_cmd_newacronym{
   local($_) = @_;
   local($cmdname,$pat,$abbrv,$long,$glsentry,$name);

   ($cmdname,$pat) = &get_next_optional_argument;

   $abbrv = &missing_braces unless
        (s/$next_pair_pr_rx/$abbrv=$2;''/eo);
   $long = &missing_braces unless
        (s/$next_pair_pr_rx/$long=$2;''/eo);
   $glsentry = &missing_braces unless
        (s/$next_pair_pr_rx/$glsentry=$2;''/eo);

   if ($cmdname eq '')
   {
      $cmdname = $abbrv;
   }

   local($id);
   $id = ++$global{'max_id'};
   local($fmtedabbrv) = &translate_commands("\\acronymfont$OP$id$CP$abbrv$OP$id$CP");

   unless ($glsentry=~/name=/)
   {
      $name = $acronymnamefmt;
      $name=~s/<tex2html_GLOSHORT_mark>/$fmtedabbrv/egs;
      $name=~s/<tex2html_GLOLONG_mark>/$long/egs;
      $id = ++$global{'max_id'};
      $glsentry .= ",name=$OP$id$CP$name$OP$id$CP";
   }

   $global{"${cmdname}first"} = 1;
   $acronym{$cmdname}{'abbrv'} = $abbrv;
   $acronym{$cmdname}{'long'} = $long;
   $acronym{$cmdname}{'entry'} = $glsentry;

   local($tmp);

   unless ($cmdname=~/[^a-zA-Z]/)
   {
      $tmp = 'sub do_cmd_' . $cmdname . '{';
      $tmp .= 'local($_)=@_;';
      $tmp .= 'local($id)=++$global{\'max_id\'};';
      $tmp .= 'local($str);';
      $tmp .= '$str="${OP}$id${CP}'
            . $cmdname
            . '${OP}$id${CP}";';
      $tmp .= '&do_cmd_useacronym($str . $_[0])';
      $tmp .= '}';

      eval($tmp);

      $tmp = 'sub do_cmd_' . $cmdname . 'star{';
      $tmp .= 'local($_)=@_;';
      $tmp .= 'local($id)=++$global{\'max_id\'};';
      $tmp .= 'local($str);';
      $tmp .= '$str="${OP}$id${CP}'
            . $cmdname
            . '${OP}$id${CP}";';
      $tmp .= '&do_cmd_useacronymstar($str . $_[0])';
      $tmp .= '}';

      eval($tmp);

      $tmp = 'sub do_cmd_' . $cmdname . 'long{';
      $tmp .= 'local($_)=@_;';
      $tmp .= 'join("", \'' . $long . '\', $_[0])';
      $tmp .= '}';

      eval($tmp);

      $tmp = 'sub do_cmd_' . $cmdname . 'short{';
      $tmp .= 'local($_)=@_;';
      $tmp .= 'join("", \'' . $fmtedabbrv . '\', $_[0])';
      $tmp .= '}';

      eval($tmp);
   }

   $_;
}

sub do_cmd_acrsh{
   local($_) = @_;
   local($cmdname,$text,$id);

   $cmdname = &missing_braces unless
                (s/$next_pair_pr_rx/$id=$1;$cmdname=$2;''/eo);

   $text = &translate_commands("\\${cmdname}short");

   $text . $_;
}

sub do_cmd_acrshstar{
   local($_) = @_;
   local($cmdname,$text,$id);

   $cmdname = &missing_braces unless
                (s/$next_pair_pr_rx/$id=$1;$cmdname=$2;''/eo);

   $text = &translate_commands("\\${cmdname}short");

   $text=~s/(<.*>)?(\w)/\1\u\2/;

   $text . $_;
}

sub do_cmd_acrln{
   local($_) = @_;
   local($cmdname,$text,$id);

   $cmdname = &missing_braces unless
                (s/$next_pair_pr_rx/$id=$1;$cmdname=$2;''/eo);

   $text = &translate_commands("\\${cmdname}long");

   $text . $_;
}

sub do_cmd_acrlnstar{
   local($_) = @_;
   local($cmdname,$text,$id);

   $cmdname = &missing_braces unless
                (s/$next_pair_pr_rx/$id=$1;$cmdname=$2;''/eo);

   $text = &translate_commands("\\${cmdname}long");

   $text=~s/(\w)/\u\1/;

   $text . $_;
}

sub do_cmd_useacronym{
   local($_)=@_;
   local($str,$abbrv,$long,$entry,$id);

   local($optarg,$pat)=&get_next_optional_argument;

   $cmdname = &missing_braces unless
                (s/$next_pair_pr_rx/$cmdname=$2;''/eo);

   if (defined %{$acronym{$cmdname}})
   {
      $abbrv = $acronym{$cmdname}{'abbrv'};
      $long = $acronym{$cmdname}{'long'};
      $entry = $acronym{$cmdname}{'entry'};
      $id = ++$global{'max_id'};
      $abbrv = "\\acronymfont$OP$id$CP$abbrv$OP$id$CP";

      $id = ++$global{'max_id'};
      $str = "\\xglossary${OP}$id${CP}type="
        . $acronymtype. "${OP}$id${CP}";
      $id = ++$global{'max_id'};
      $str .= "${OP}$id${CP}"
        . $entry . "${OP}$id${CP}";
      $id = ++$global{'max_id'};
      $str .= "${OP}$id${CP}";
      $str .= ($global{"${cmdname}first"} ? "$long$optarg ($abbrv)" : "$abbrv$optarg");
      $str .= "${OP}$id${CP}";

      $global{"${cmdname}first"} = 0;
   }
   else
   {
      &write_warnings("acronym '$cmdname' not defined");
   }

   $str . $_
}

sub do_cmd_useacronymstar{
   local($_)=@_;
   local($str,$abbrv,$long,$entry,$id);
   local($optarg,$pat)=&get_next_optional_argument;

   $cmdname = &missing_braces unless
               (s/$next_pair_pr_rx/$cmdname=$2;''/eo);

   if (defined %{$acronym{$cmdname}})
   {
      $abbrv = $acronym{$cmdname}{'abbrv'};
      $long = $acronym{$cmdname}{'long'};
      $entry = $acronym{$cmdname}{'entry'};

      if ($global{"${cmdname}first"})
      {
         $long=~s/^([^a-zA-Z]*)([a-zA-Z])/\1\u\2/;
      }
      else
      {
         $abbrv=~s/^([^a-zA-Z]*)([a-zA-Z])/\1\u\2/;
      }

      $id = ++$global{'max_id'};
      $abbrv = "\\acronymfont$OP$id$CP$abbrv$OP$id$CP";

      $name = ($global{"${cmdname}first"} ? "$long$optarg ($abbrv)" : "$abbrv$optarg");

      $id = ++$global{'max_id'};
      $str = "\\xglossary${OP}$id${CP}type="
        . $acronymtype . "${OP}$id${CP}";
      $id = ++$global{'max_id'};
      $str .= "${OP}$id${CP}"
        . $entry . "${OP}$id${CP}";
      $id = ++$global{'max_id'};
      $str .= "${OP}$id${CP}";
      $str .= $name;
      $str .= "${OP}$id${CP}";

      $global{"${cmdname}first"} = 0;
   }
   else
   {
      &write_warnings("acronym '$cmdname' not defined");
   }

   $str . $_
}

sub do_cmd_ifacronymfirstuse{
   local($_) = @_;
   local($acronym,$truebit,$falsebit,$str);

   $acronym = &missing_braces unless ($_[0]=~s/$next_pair_pr_rx//o&&($acronym=$2));
   $truebit = &missing_braces unless ($_[0]=~s/$next_pair_pr_rx//o&&($truebit=$2));
   $falsebit = &missing_braces unless ($_[0]=~s/$next_pair_pr_rx//o&&($falsebit=$2));

   $str = ($global{"${acronym}true"} ? $truebit : $falsebit);

   $str . $_[0];
}

sub do_cmd_resetacronym{
   local($_) = @_;
   local($cmdname);

   $cmdname = &missing_braces unless
               (s/$next_pair_pr_rx/$cmdname=$2;''/eo);

   if (defined %{$acronym{$cmdname}})
   {
      $global{"${cmdname}first"} = 1;
   }
   else
   {
      &write_warnings("acronym '$cmdname' not defined");
   }

   $_;
}

sub do_cmd_resetallacronyms{
   local($_) = @_;

   foreach $key (keys %acronym)
   {
      $global{"${key}first"} = 1;
   }

   $_;
}

sub do_cmd_unsetacronym{
   local($_) = @_;
   local($cmdname);

   $cmdname = &missing_braces unless
               (s/$next_pair_pr_rx/$cmdname=$2;''/eo);

   if (defined %{$acronym{$cmdname}})
   {
      $global{"${cmdname}first"} = 0;
   }
   else
   {
      &write_warnings("acronym '$cmdname' not defined");
   }

   $_;
}

sub do_cmd_unsetallacronyms{
   local($_) = @_;

   foreach $key (keys %acronym)
   {
      $global{"${key}first"} = 0;
   }

   $_;
}

 %savedglosentry = ();

# This command is deprecated
sub do_cmd_saveglosentry{
   local($_) = @_;
   local($name,$desc,$type,$pat);

   ($type,$pat) = &get_next_optional_argument;

   $name = &missing_braces unless
             s/$next_pair_pr_rx/$name=$2;''/eo;
   $desc = &missing_braces unless
             s/$next_pair_pr_rx/$desc=$2;''/eo;

   $savedglosentry{$name}{'entry'} = "name=$name,description=$desc";
   $savedglosentry{$name}{'type'} = $type;

   $_;
}

sub do_cmd_storeglosentry{
   local($_) = @_;
   local($type,$pat,$entry,$label);

   ($type,$pat) = &get_next_optional_argument;

   if ($type eq '')
   {
      $type = 'glossary';
   }

   $label = &missing_braces unless
              s/$next_pair_pr_rx/$label=$2;''/eo;

   $entry = &missing_braces unless
              s/$next_pair_pr_rx/$entry=$2;''/eo;

   $savedglosentry{$label}{'entry'} = $entry;
   $savedglosentry{$label}{'type'} = $type;

   $_;
}

sub do_cmd_useglosentry{
   local($_) = @_;
   local($optarg,$pat,$name,$str,$id);
   ($optarg,$pat) = &get_next_optional_argument;

   $name = &missing_braces unless
             (s/$next_pair_pr_rx/$name=$2;''/eo);

   if (defined $savedglosentry{$name}{type})
   {
      $id = ++$global{'max_id'};
      $str = "\\$savedglosentry{$name}{type}${OP}$id${CP}$savedglosentry{$name}{entry}";

      unless ($optarg eq "")
      {
         $str .= ",$optarg";
      }

      $str .= "${OP}$id${CP}";
   }
   else
   {
      &write_warnings("glossary entry '$name' undefined");
      $str = '';
   }

   $str . $_;
}

sub do_cmd_useGlosentry{
   local($_) = @_;
   local($optarg,$pat,$name,$str,$id);
   ($optarg,$pat) = &get_next_optional_argument;

   $name = &missing_braces unless
             (s/$next_pair_pr_rx/$name=$2;''/eo);

   if (defined $savedglosentry{$name}{type})
   {
      $id = ++$global{'max_id'};
      $str = "\\x$savedglosentry{$name}{type}${OP}$id${CP}$savedglosentry{$name}{entry}";

      unless ($optarg eq "")
      {
         $str .= ",$optarg";
      }

      $str .= "${OP}$id${CP}";
   }
   else
   {
      &write_warnings("glossary entry '$name' undefined");
      $str = '';
   }

   $str . $_;
}

sub do_cmd_gls{
   local($_) = @_;
   local($optarg,$pat,$label,$str,$id,$name);
   ($optarg,$pat) = &get_next_optional_argument;

   $label = &missing_braces unless
             (s/$next_pair_pr_rx/$label=$2;''/eo);

   if (defined $savedglosentry{$label}{type})
   {
      $str = $savedglosentry{$label}{'entry'};

      if ($str=~/name=[ ]*${OP}(\d+)${CP}(.*)${OP}\1${CP}/s)
      {
         $name = $2;
      }
      elsif (($str=~/name=[ ]*([^,]+),/m)
          || ($str=~/name=[ ]*([^,]+)\Z(?!\n)/m))
      {
         $name = $1;
      }

      $id = ++$global{'max_id'};
      $str = "\\x$savedglosentry{$label}{type}${OP}$id${CP}$savedglosentry{$label}{entry}";

      unless ($optarg eq "")
      {
         $str .= ",$optarg";
      }

      $str .= "${OP}$id${CP}";
      $id = ++$global{'max_id'};
      $str .= "${OP}$id${CP}$name${OP}$id${CP}";
   }
   else
   {
      &write_warnings("glossary entry '$label' undefined");
      $str = '';
   }

   $str . $_;
}

sub do_cmd_glossarypreamble{
   local($_) = @_;
   $_[0];
}

sub do_cmd_glossarypostamble{
   local($_) = @_;
   $_[0];
}

sub do_cmd_glsnumformat{
   local($_) = @_;
   local($type,$pat) = &get_next_optional_argument;

   if ($type eq '')
   {
      $type = 'glossary';
   }

   local($cmd) = '';
   unless ($glsnumformat{$type} eq '')
   {
      $cmd = "\\$glsnumformat{$type}";
   }

   $cmd . $_;
}

sub do_cmd_setglossary{
   local($_) = @_;
   local($str,$type,$format,$delimN,$glodelim);
   $str = &missing_braces unless ($_[0]=~s/$next_pair_pr_rx//o&&($str=$2));

   unless (($str=~/type=([^,]+),|$/&&($type=$1)) ||
    ($str=~/type=${OP}(\d+)${CP}(.*)${OP}\1${CP}/&&($type=$2)))
   {
      $type = 'glossary';
   }

   if ($str=~/glsnumformat=[ ]*${OP}(\d+)${CP}(.*)${OP}\1${CP}/s)
   {
      $format = $2;
   }
   elsif (($str=~/glsnumformat=[ ]*([^,]+),/m)
       || ($str=~/glsnumformat=[ ]*([^,]+)\Z(?!\n)/m))
   {
      $format = $1;
   }

   if ($format ne '')
   {
      $glsnumformat{$type} = $format;

      if ($format eq 'ignore')
      {
         $delimN{$type} = '';
      }
   }

   if (($str=~/delimN=([^,]+),|$/&&($delimN=$1)) ||
    ($str=~/delimN=${OP}(\d+)${CP}(.*)${OP}\1${CP}/&&($delimN=$2)))
   {
      $delimN{$type} = $delimN;
   }

   if (($str=~/glodelim=([^,]+),|$/&&($glodelim=$1)) ||
    ($str=~/glodelim=${OP}(\d+)${CP}(.*)${OP}\1${CP}/&&($glodelim=$2)))
   {
      $glodelim{$type} = $glodelim;
   }

   $_[0];
}

sub do_cmd_ignore{
   local($_) = @_;
   local($str);
   $str = &missing_braces unless ($_[0]=~s/$next_pair_pr_rx//o&&($str=$2));

   $_[0];
}

sub do_cmd_hyperit{
   join('', "\\textit ", $_[0]);
}

sub do_cmd_hyperrm{
   join('', "\\textrm ", $_[0]);
}

sub do_cmd_hypertt{
   join('', "\\texttt ", $_[0]);
}

sub do_cmd_hypersf{
   join('', "\\textsf ", $_[0]);
}

sub do_cmd_hyperbf{
   join('', "\\textbf ", $_[0]);
}

&ignore_commands( <<_IGNORED_CMDS_ );
makeglossary
makeacronym
_IGNORED_CMDS_

1;
