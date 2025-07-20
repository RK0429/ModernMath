-- Quarto filter to automatically add translation status badges

local yaml = require('lyaml')

function read_translation_status()
  local file = io.open("translations-status.yml", "r")
  if not file then
    return nil
  end

  local content = file:read("*all")
  file:close()

  return yaml.load(content)
end

function Meta(meta)
  -- Try to determine the current file from metadata
  if meta.title then
    -- Add translation status information to the metadata
    local status_data = read_translation_status()
    if status_data then
      -- This is where we would look up the current file's translation status
      -- and add it to the metadata for use in templates
      meta.translation_status = pandoc.MetaMap({
        available = pandoc.MetaBool(true)
      })
    end
  end
  return meta
end
