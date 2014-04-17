#!/usr/bin/perl

# File    : makeglos
# Author  : Nicola Talbot
# Version : 1.5 (2006/07/20)
# Description: simple Perl script that calls makeindex.
# Intended for use with "glossary.sty" (saves having to remember
# all the various switches)

use Getopt::Std;

if ($#ARGV < 0)
{
   die "Syntax : $0 [-ilqrcgm] [-s sty] [-o gls] [-t log] [-p num] <filename>\n";
}

getopt('sotp');
getopts('ilqrcgm');

# define known extensions

 %exttype = (
   glossary => {in=>'glo', out=>'gls', 'log'=>'glg'},
 );

$ext = '';

if (length(@ARGV[0]) < 4)
{
   $name = @ARGV[0];
}
elsif (substr(@ARGV[0],-4,1) eq ".")
{
  $name = substr(@ARGV[0],0,length(@ARGV[0])-4);

  $ext = substr(@ARGV[0],-3,3);
}
else
{
   $name = @ARGV[0];
}

$istfile = "$name.ist";

# check log file for other glossary types
# and for ist file name

if (open AUXFILE, "$name.aux")
{
   while (<AUXFILE>)
   {
      if (m/\\\@newglossarytype\s*\[(.*)\]{(.*)}{(.*)}{(.*)}/)
      {
         $exttype{$2}{'in'}  = $3;
         $exttype{$2}{'out'} = $4;
         $exttype{$2}{'log'} = $1;

         if (!$opt_q)
         {
            print "added glossary type '$2' ($3,$4,$1)\n";
         }
      }

      if (m/\\\@istfilename\s*{([^}]*)}/)
      {
         $istfile = $1;
      }
   }

   close AUXFILE;
}
else
{
   print "unable to open $name.aux\n";
}

# save all the general makeindex switches

$mkidxopts = '';

if ($opt_i)
{
   $mkidxopts .= " -i";
}

if ($opt_l)
{
   $mkidxopts .= " -l";
}

if ($opt_q)
{
   $mkidxopts .= " -q";
}

if ($opt_r)
{
   $mkidxopts .= " -r";
}

if ($opt_c)
{
   $mkidxopts .= " -c";
}

if ($opt_g)
{
   $mkidxopts .= " -g";
}

unless ($opt_p eq "")
{
   $mkidxopts .= " -p $opt_p";
}

unless ($opt_s eq "")
{
   $istfile = $opt_s;
}

if ($ext ne '')
{
   %thistype = %{$exttype{'glossary'}}; #default

   foreach $type (keys %exttype)
   {
      if ($exttype{$type}{'in'} eq $ext)
      {
         %thistype = %{$exttype{$type}};

         last;
      }
   }

   if ($opt_o eq "")
   {
      $outfile = "$name.$thistype{out}";
   }
   else
   {
      $outfile = $opt_o;
   }

   if ($opt_t eq "")
   {
      $transcript = "$name.$thistype{'log'}";
   }
   else
   {
      $transcript = $opt_t;
   }

   &makeindex("$name.$ext",$outfile,$transcript,$istfile,
              $mkidxopts,$opt_q,$opt_m);
}
else
{
   foreach $type (keys %exttype)
   {
      %thistype = %{$exttype{$type}};

      $inputfile = "$name.$thistype{in}";

      if (-r $inputfile)
      {
         if ($opt_o eq "")
         {
            $outfile = "$name.$thistype{out}";
         }
         else
         {
            $outfile = $opt_o;
         }

         if ($opt_t eq "")
         {
            $transcript = "$name.$thistype{'log'}";
         }
         else
         {
           $transcript = $opt_t;
         }

         &makeindex($inputfile,$outfile,$transcript,
                    $istfile,$mkidxopts,$opt_q,$opt_m);
      }
      elsif (!$opt_q)
      {
         print "no read access for '$inputfile'\n";
      }
   }
}

sub makeindex{
   local($in,$out,$trans,$ist,$rest,$quiet,$merge) = @_;
   local($name,$cmdstr,$buffer,$n,$i,$j);
   local(@stuff,@item);

   if ($merge)
   {
      $cmdstr = "$rest -s $ist -t $trans -o tmp_$out $in";
   }
   else
   {
      $cmdstr = "$rest -s $ist -t $trans -o $out $in";
   }

   unless ($quiet)
   {
      print "makeindex $cmdstr\n";
   }

   `makeindex $cmdstr`;

   if ($merge)
   {
      print "Merging entries\n";

      open INPUT, "<tmp_$out";

      $buffer = "";

      while (<INPUT>)
      {
         $buffer .= $_;
      }

      close INPUT;

      open OUTPUT, ">$out";

      @stuff = split /\\gloitem /, $buffer;

      $n = scalar(@stuff);

      if ($n < 2)
      {
         print OUTPUT $buffer;
      }
      else
      {
         print OUTPUT $stuff[0];

         for ($i = 1, $j=-1; $i < $n; $i++)
         {
            if ($stuff[$i]=~s/{\\glosslabel{(.+)}{(.+)}}//)
            {
               $name = $&;

               if ($j==-1)
               {
                  $j = 0;
                  $item[0]{'name'} = $name;
                  $item[0]{'desc'} = $stuff[$i];
               }
               else
               {
                  # makeindex has already sorted the entries
                  # alphabetically, so duplicate entries
                  # will be one after the other

                  if ($item[$j]{'name'} eq $name)
                  {
                     $item[$j]{'desc'} .= $stuff[$i];

                     print "collating $name\n";
                  }
                  else
                  {
                     $j++;
                     $item[$j]{'name'} = $name;
                     $item[$j]{'desc'} = $stuff[$i];
                  }
               }
            }
            else
            {
               print STDERR
                     "unable to extract name from glossary item:\n",
                      $stuff[$i];
            }
         }

         for ($i=0; $i <= $j; $i++)
         {
            # remove all but the last \delimT
            while ($item[$i]{'desc'}=~s/\\delimT/$&/sg > 1)
            {
               $item[$i]{'desc'}=~s/\\delimT//s;
            }
            print OUTPUT "\\gloitem ", $item[$i]{'name'},
                        $item[$i]{'desc'};
         }
      }

      close OUTPUT;

      print "Output written in $out\n";

      unlink "tmp_$out" or print "Can't delete tmp_$out: $!\n";
   }
}

1;
