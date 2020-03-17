// Version d'OpenGL
#version 330

in vec2 vert_texCoord;
in vec3 vert_normal;
in vec3 light_dir;
in vec3 view_dir;

out vec4 frag_color;
uniform sampler2D texSampler;

// Pour Blinn-Phong :
vec3 ambiant;
vec3 diffus;
uniform float pa = 0.2;
float pd;
vec3 Lf;

// Fonction appellee pour chaque fragment
void main() {
  vec3 normal = normalize(vert_normal);

  float t = dot(-light_dir, normal);
  t = max(t, 0.0);

  // Pour Blinn-Phong :
  pd = vec3(texture(texSampler, vert_texCoord)).y;
  ambiant = pa * vec3(texture(texSampler, vert_texCoord));
  diffus = pd * vec3(texture(texSampler, vert_texCoord))*t;
  Lf = ambiant + diffus;

  // Affectation de la couleur du fragment
  // vec3 color = vec3(vert_texCoord.xy, 0.5);
  // frag_color = vec4(color, 1.0);                // dégradé
  frag_color = texture(texSampler, vert_texCoord); // texture simple
  // frag_color = vec4(Lf, 1.0);                   // pour Blinn-Phong
}
