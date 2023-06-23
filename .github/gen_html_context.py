import os, sys

# Run this script from one of the doc checkout dirs RefMan doc dir
# (e.g. docs/ci_build_out/DIR/docs/RefMan})
#
# Arguments: owner/repository current_version

d = os.listdir('../../..')
bldtgt = lambda n: os.path.join('/', sys.argv[1].split('/')[1], n, 'RefMan.html')

html_context={'current_version': sys.argv[2],
              'versions':sorted([(v, bldtgt(v)) for v in d if not v.startswith('PR_')]),
              'pull_reqs':sorted([(v, bldtgt(v)) for v in d if v.startswith('PR_')])}

if not os.path.isdir('_templates'):
    # Older versions of the repo do not have this file present as it was only
    # added in the global gh_pages support, so manually generate it here.  This
    # is a duplicate of the existing _templates/versions.html.  Having it as an
    # explicit HTML file will be easier to find and work with in the future,
    # which is why this generator isn't the sole location of this HTML, at the
    # cost of duplication.
    #
    # Once there are no pull requests that originated from before the latter file
    # was part of master, this duplication here can be removed.
    os.mkdir('_templates')
    open('_templates/versions.html', 'w').write('''
<div class="rst-versions" data-toggle="rst-versions" role="note" aria-label="{{ _('Versions') }}">
  <span class="rst-current-version" data-toggle="rst-current-version">
    <span class="fa fa-book">Doc version</span>
    v: {{ current_version }}
    <span class="fa fa-caret-down"></span>
    <div class="rst-other-versions">
      <dl>
        <dt>{{ _('Versions') }}</dt>
        {% for slug, url in versions %}
        <dd><a href="{{ url }}">{{ slug }}</a></dd>
        {% endfor %}
      </dl>
      <dl>
        <dt>{{ _('Pull Requests') }}</dt>
        {% for slug, url in pull_reqs %}
        <dd><a href="{{ url }}">{{ slug }}</a></dd>
        {% endfor %}
      </dl>
    </div>
  </span>
</div>
''')

print('html_context=',html_context)
