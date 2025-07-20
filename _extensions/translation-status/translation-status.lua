-- Quarto extension for translation status badges

function translation_status(args)
  local status = pandoc.utils.stringify(args[1])
  local badge_html = ""

  if status == "completed" then
    badge_html = '<span class="badge bg-success">Translated</span>'
  elseif status == "needs_update" then
    badge_html = '<span class="badge bg-warning">Needs Update</span>'
  elseif status == "in_progress" then
    badge_html = '<span class="badge bg-info">In Progress</span>'
  else
    badge_html = '<span class="badge bg-secondary">Not Translated</span>'
  end

  return pandoc.RawInline('html', badge_html)
end
